"""
Name: 'CutAndUnfold'
Blender: 278
Group: 'AddMesh'
Tip: 'Cuts the Active mesh along seams and unfolds resulting parts'
test de modification du 29/07/2017
"""

import bpy
import sys
#will unfold active mesh object
#only works with triangle faces
from mathutils import Vector, Matrix
from math import *
import xml.sax, xml.sax.saxutils

objet_actif = bpy.context.active_object
print("objet_actif : ", objet_actif)
print("objet_actif.type : ", objet_actif.type)
if objet_actif.type == "MESH" : mesh_to_unfold = objet_actif.data
else : 
    print("sélectionner d'abord un objet mesh")
    
print("mesh_to_unfold : ", mesh_to_unfold)
for fa in mesh_to_unfold.polygons : 
    print("fa : ", fa)
    print("fa.index : ", fa.index, "; fa.loop_total : ", fa.loop_total)
    vpi = 0 #vpi : Vertex Polygon Index (index du vertex relatif au polygon)
    for vmi in fa.vertices : #vmi : Vertex Mesh Index (index du vertex par rapport au mesh, index absolu)
        print("vpi : ", vpi, "; vmi : ", vmi)
        vpi += 1
for ve in mesh_to_unfold.vertices : 
    print("ve : ", ve)
    print("ve.index : ", ve.index, " (", ve.co.x, ", ", ve.co.y, ", ", ve.co.z, ")")

class UnfoldedObject :
    """
    19/07/2017: projet de clarification du code
    """
    def __init__(self, sourceObject) :
        self.sourceObject = sourceObject
        self.islands = [] # Liste des îlots qui résulterons du dépliage

class face_relationships :
    def __init__(self,indexsrcface,parentface) :
        self.srcfaceindex = indexsrcface #index du polygone dans le maillage source 
        self.srcfacevertsindexes = [] #liste des vertices du polygone dans le maillage source.
        self.destfaceindex = None # cet attribut sera renseigné si la face candidate est admise dans l'ilot, 
                                  # c'est l'index de la face correspondante dans le maillage déplié.
        self.destfacevertsindexes = []
        self.newverts =[]
        self.parentface_relationships = parentface
        self.exploredadjacentfacesindexes = [] # cette liste contiendra au minimum la face parente s'il y en a une
        if not(parentface == None) : 
            # dés la création on ajoute la nouvelle faces dans la liste des faces adjacentes explorées de son parent
            # ainsi m^eme si cette face n'est pas admise dans l'ilot,
            # elle ne sera plus candidate en tant que face adjacente de cette face parente.
            # m^eme s'il est possible que plus tard, elle soit à nouveau candidate à ce me^me ilot, 
            # mais en tant que face adjacente d'un autre parent
            parentface.exploredadjacentfacesindexes.append(self.srcfaceindex)
            # A priori, seulement utile si la face est admise dans l'ilot, mais au moins, c'est fait
            self.exploredadjacentfacesindexes.append(parentface.srcfaceindex)
    
    def FindAdjacent(self):
        """
        on recherche les faces adjacentes parmi les faces non déjà traitées (donc figurant dans la liste faces_to_unfold)
        et n'ayant pas déja été candidate en tant que enfant de la face explorée
        (donc ne figurant pas dans la liste self.exploredadjacentfacesindexes) 
        """
        global faces_to_unfold, mesh_to_unfold
        parentfa = mesh_to_unfold.polygons[self.srcfaceindex]
        print("recherche de face adjacente pour la face ", self.srcfaceindex, mesh_to_unfold.polygons[self.srcfaceindex])
        parentverts_set = set([ve for ve in parentfa.vertices])
        forbiddenfaces = [self.srcfaceindex]
        forbiddenfaces.extend(self.exploredadjacentfacesindexes)
        print("faces interdites =", forbiddenfaces)
        for fi in faces_to_unfold :
            if fi not in forbiddenfaces :
                fa = mesh_to_unfold.polygons[fi]
                faverts_set = set([ve for ve in fa.vertices])
                inter_set = parentverts_set&faverts_set
                if len(inter_set) == 2 :
                    # on recherche l'arete correspondante pour vérifier si c'est une couture
                    for ed in mesh_to_unfold.edges :
                        if len(inter_set&set([ed.vertices[0], ed.vertices[1]]))==2 : 
                            if not(ed.use_seam) :
                                print("face trouvee = ", fi)
                                return fi
                
    def IsAdmited(self):
        global faces_to_unfold, mesh_to_unfold, island_verts, island_faces
        if (self.parentface_relationships == None) : 
            root=True
            print("La face ", self.srcfaceindex, " est la racine de son îlot.")
        else : 
            root = False
            print("La face ",self.srcfaceindex, "est l'enfant de la face", self.parentface_relationships.srcfaceindex)
        fa = mesh_to_unfold.polygons[self.srcfaceindex] 
        if root :
            def minz(vertice) :
                """
                trouve parmi une liste d'indices de vertices, l'indice du vertex dont la coordonée z est la plus basse              
                """
                #global mesh_to_unfold
                lowestve_meshindice = vertice[0] #indice par rapport au mesh du vertice le plus bas (ie dont la coordonnée z est  la plus petite)
                lowestve_faindice = 0 #indice par rapport au poly de l'indice par rapport au mesh du vertice le plus bas
                for i,ve in enumerate(vertice) :
                    if mesh_to_unfold.vertices[ve].co[2]<=mesh_to_unfold.vertices[lowestve_meshindice].co[2] : 
                        lowestve_faindice = i
                        lowestve_meshindice = ve
                return (lowestve_meshindice, lowestve_faindice)

            #choix du premier vertex de référence
            #celui qui va définir la translation qu'on va appliquer à la face
            #pour que ce premier vertex de référence se retrouve dans le plan z=0
            vertref1_meshindice = minz(fa.vertices)[0]
            vertref1 = mesh_to_unfold.vertices[vertref1_meshindice] #de la classe MeshVertex
            #calcul des vecteurs de départ et d'arrivée de la transtation
            v1 = Vector(vertref1.co)
            v2 = Vector((vertref1.co.x,vertref1.co.y, 0)) #v2 projection de v1 sur le plan z=0
            vertref1_faindice = minz(fa.vertices)[1]
        else :
            #si la face courante a déjà une face parente dans l'îlot,
            #on recherche l'arête commune entre la face courante et la face parente.
            parentfa = mesh_to_unfold.polygons[self.parentface_relationships.srcfaceindex]
            commonedgevertice_meshindexes = [] #les indices absolus des 2 vertices de l'arête commune
            commonedgevertice_faindexes = [] #les indices des 2 vertices de l'arête commune dans la face courante
            commonedgevertice_parentfaindexes = [] #les indices des 2 vertices de l'arête commune dans la face parente
            for i,vi in enumerate(fa.vertices) :
                for j,vj in enumerate(parentfa.vertices) :
                    if (vi == vj) : 
                        commonedgevertice_meshindexes.append(vi)
                        commonedgevertice_faindexes.append(i)
                        commonedgevertice_parentfaindexes.append(j)
            vertref1_meshindice = commonedgevertice_meshindexes[0] #index absolu du premier vertex de l'arête commune
            print("index absolu du premier vertex de l'arête commune : ", vertref1_meshindice)
            v1 = Vector(mesh_to_unfold.vertices[vertref1_meshindice].co)
            vertref1_parentfaindice = commonedgevertice_parentfaindexes[0] #index relatif à la face parente, du premier vertex de l'arête commune 
            v2 = Vector(island_verts[self.parentface_relationships.destfacevertsindexes[vertref1_parentfaindice]][1])
            vertref1_faindice = commonedgevertice_faindexes[0] #index relatif à la face courante, du premier vertex de l'arête commune 
                        
        #calcul du vecteur de translation   
        vt = v2-v1  
        #calcul des vertices translatés de la face courante
        vectors = [Vector(mesh_to_unfold.vertices[ve].co)+vt for ve in fa.vertices]
        print("vectors après translation: ", vectors)

        if root :
            #choix du deuxième vertex de référence, 
            #celui qui va définir la 1ère rotation qu'on va appliquer aux vertice de la face    
            #cette rotation appliquée au deuxième vertex de référence va le ramener dans le plan z=0
            possiblechoices = [i for i in range(len(vectors))]
            possiblechoices.remove(vertref1_faindice) # on écarte le vertex qui vient d'être translaté dans le plan z=0
            for i in possiblechoices : # on écarte également un éventuel vertex qui serait à la verticale du 1er vertex de référence
                if (vectors[i].x == v2.x) and (vectors[i].y == v2.y) :
                    possiblechoices.remove(i)
            vertref2_faindice = possiblechoices[0] # sachant qu'on ne traite que des faces triangulaires, il reste 1 ou 2 choix possible, on prend arbitrairement le premier
            for i in possiblechoices : # et on le compare au 2eme (s'il y en a un pour choisir celui qui est le plus près du plan z=0
                if abs(vectors[i].z) <= abs(vectors[vertref2_faindice].z) : vertref2_faindice = i
    
            #calcul des vecteurs définissant la 1ere rotation
            v1 = vectors[vertref2_faindice]-vectors[vertref1_faindice]
            pvertref2 = Vector((vectors[vertref2_faindice].x, vectors[vertref2_faindice].y, 0))     #projection de vertref2 sur le plan z=0
            v2 = pvertref2-vectors[vertref1_faindice]
        else:
            vertref2_faindice   = commonedgevertice_faindexes[1] #index relatif à la face courante du deuxième vertex de l'arête commune
            v1 = vectors[vertref2_faindice]-vectors[vertref1_faindice]
            print("v1 = ", v1)
            v2 = Vector(island_verts[self.parentface_relationships.destfacevertsindexes[commonedgevertice_parentfaindexes[1]]][1])-vectors[vertref1_faindice]
            print("v2 = ", v2) # transformé du 2eme vertex de l'arête commune
            
        #calcul de la matrice de rotation
        angle12 = v1.angle(v2)
        print("angle de rotation : ", angle12)
        
        #calcul de l'axe de rotation
        v12 = v1.cross(v2)
        print("axe de rotation : ", v12)
    
        #calcul de la matrice de rotation
        rot1mat = Matrix.Rotation(angle12, 3, v12)
        print("matrice de rotation : ", rot1mat)

        def TransformVectors(vecs,vt,rotmat) :
            """
            applique successivement une translation vt, une rotation rotmat, 
            et la translation inverse à tous les vecteurs de la liste vecs
            """
            vecs1 = [v+vt for v in vecs]
            vecs2 = [rotmat*v for v in vecs1]
            vecs3 = [v-vt for v in vecs2]
            return vecs3

        #applications de la transformation en 3 étapes
        #translation vers l'origine de sorte que le 1er vertex de référence soit inchangé par la rotation
        #rotation qui amène le 2eme vertex de référence dans le plan z=0, puis translation inverse
        vectors = TransformVectors(vectors, -vectors[vertref1_faindice],rot1mat)
        print("vectors après rotation 1 == ", vectors)

        #choix du 3eme vertex de reférence
        possiblechoices = [i for i in range(len(vectors))]
        possiblechoices.remove(vertref1_faindice)
        possiblechoices.remove(vertref2_faindice)
        vertref3_faindice = possiblechoices[0]
        print("ordre des indices = ", vertref1_faindice, ", ", vertref2_faindice, ", ", vertref3_faindice)

        #on veut poser la face sur le plan z=0 de sorte que sa normale pointe vers le haut
        #or on connait la normale de la face avant transformation 
        #mais pas après les transformations qui viennent d'etre faite
        #on va donc comparer la normale avec le produit vectoriel des vecteurs v12(vertref1, vertref2) et v13(vertref1, vertref3)
        #et en fonction du résultat de la comparaison, 
        #c'est soit le produit vectoriel des vecteurs transformés
        #soit le vecteur inverse qui servira au calcul de l'angle de rotation
        vertref1_meindice = fa.vertices[vertref1_faindice] #on retrouve l'indice absolu du vertref1 à partir de son indice par rapport à la face courante
        vertref2_meindice = fa.vertices[vertref2_faindice]
        vertref3_meindice = fa.vertices[vertref3_faindice]
        print("indice absolu de vertref1 : ", vertref1_meindice, "vérification : ", vertref1_meshindice)
        print("indice absolu de vertref2 : ", vertref2_meindice)
        print("indice absolu de vertref3 : ", vertref3_meindice)
        vi1 = Vector(mesh_to_unfold.vertices[vertref1_meindice].co) #vecteur initial 1 représentant le vertref1 avant transformation
        vi2 = Vector(mesh_to_unfold.vertices[vertref2_meindice].co)
        vi3 = Vector(mesh_to_unfold.vertices[vertref3_meindice].co)
        print("vi1 : ", vi1)
        print("vi2 : ", vi2)
        print("vi3 : ", vi3)
        vi12 = vi2-vi1
        print("vi12 : ", vi12)
        vi13 = vi3-vi1
        print("vi13 : ", vi13)
        vi12vi13 = vi12.cross(vi13)
        print("vi12vi13 : ", vi12vi13)
        angle_vi12vi13_no = vi12vi13.angle(fa.normal)       
        if (angle_vi12vi13_no < pi) : coef = 1
        else : coef = -1 #coeficient qui déterminera l'orientation du vecteur 
        #on calcule maintenant le produit vectoriel de ces meme deux vecteurs dans leur position courante après transformation
        vc12 = vectors[vertref2_faindice]-vectors[vertref1_faindice]
        print("vc12 : ", vc12)
        vc13 = vectors[vertref3_faindice]-vectors[vertref1_faindice]
        print("vc13 : ", vc13)
        vc12vc13 = vc12.cross(vc13) 
        print("vc12vc13 : ", vc12vc13)
        vo = vc12vc13*coef #vecteur "origine" de la rotation
        print("vo : ", vo)
        vd = Vector((0,0,1)) #vecteur "destination" de la rotation
        print("vd : ", vd)
        ar = vo.angle(vd) #angle de la rotation
        print("angle de la rotation vo vd : ", ar)
        if (-0.001<ar<0.001) or (pi-0.001<ar<pi+0.001) :
            va = vc12 # dans ce cas particulier d'une rotation de 0 ou de 180p
        else :
            vod = vo.cross(vd) #pour déterminer l'orientation du vecteur axe de la rotation
            angle_vod_vc12 = vod.angle(vc12)
            if (angle_vod_vc12<pi) : va = vc12
            else : va = -vc12
        print("axe de la rotation = ", va)
        print("angle de la rotation = ", ar)
        rot2mat = Matrix.Rotation(ar,3,va)

        vectors = TransformVectors(vectors, -vectors[vertref1_faindice],rot2mat)
        print("vectors après rotation 2: ", vectors)

        if root:
            #puisque on commence un ilot, les 3 vertices de la face en cours sont nouveaux dans l'ilot
            #pour chaque vertex on renseigne son index dans le mesh source et ses coordonnées dans l'ilot en création.  
            self.newverts=[[fa.vertices[i], [vectors[i].x, vectors[i].y, vectors[i].z]] for i in range(len(fa.vertices))] 
            #définition de la 1ere face de l'ilot
            self.destfacevertsindexes = [i for i in range(len(fa.vertices))]
        else :
            for i,vi in enumerate([ve for ve in fa.vertices]) :
                if vi in commonedgevertice_meshindexes : # si le vertice appartiend à l'arête commune, on ne l'ajoute pas à newverts parce qu'il y est déjà suite au traitement de la face parente
                    refindex = commonedgevertice_meshindexes.index(vi) # index de ce vertice dans la liste des vertices de l'arête commune (0 ou 1)
                    parentfavertindex = commonedgevertice_parentfaindexes[refindex] #index de ce même vertice dans la liste des vertice de la face parente
                    self.destfacevertsindexes.append(self.parentface_relationships.destfacevertsindexes[parentfavertindex]) # l'index du vertice correspondant dans l'ilot
                else :
                    self.destfacevertsindexes.append(len(island_verts)) # creation d'un nouvel index pour ajouter ce vertex à l'ilot en cours
                    self.newverts.append([vi,[vectors[i].x, vectors[i].y, vectors[i].z]]) #on ajoute à la liste des nouveaux vertice, les vertices qui n'appartiennent pas à l'arête commune
        return True # pour l'instant on admet toutes les faces sans vérifier le chevauchement.
        # Plus tard on ajoutera une vérification pour rejeter les faces qui recouvrent les faces déjà dépliées.
        # Elles feront automatiquement partie d'un autre ilot.

    def add_to_island_faces(self, island_faces) :
        """
        19/07/2017 projet de clarification du code
        """
        self.destfaceindex = len(island_faces)
        island_faces.append(self)
        
    def add_to_island_verts(self, island_verts) :
        """
        19/07/2017 : ajoute les vertices nouvellement calculées de la face dépliée à la liste des vertices de l'îlot
        """
        island_verts.extend(self.newverts)


class bord :
    """
    un bord est une arête qui appartient à 1 et 1 seule face
    on a besoin de la notion de bords pour définir le contour d'un ilot
    """
    def __init__(self, i, ei, fi) :
        self.index = i
        self.edgeindex = ei
        self.faceindex = fi

class island:
    """
    cet objet va être utile pour l'export car on va y memoriser l'object produit par le développement d'une portion de surface et la liste des index dans le mesh source des arêtes de l'ilot.
    """
    def __init__(self, ob, edges_srcindexes) :
        self.blenderobject = ob
        self.edges_srcindexes = edges_srcindexes
        self.bords = [] # les bords sont les arêtes qui appartiennent à 1 et seulement 1 face
        self.contour = [] # le contour est une liste de vertices qu'on obtiend en ordonnançant les bords
        me = self.blenderobject.data
        #calcul des bords
        for ed in me.edges :
            e = set([ed.vertices[0],ed.vertices[1]])
            facefound = False
            faceunique = True
            for fa in me.polygons :
                f = set(fa.vertices)
                if e == e&f : # si e appartient à la face f
                    if not facefound :
                        facefound = True
                        # on défini b pour le cas ou la face trouvée serait unique
                        # si c'est le cas on l'ajoute à la liste bords (pas besoin de refaire une boucle pour le retrouver
                        # sinon on ne l'utilise pas
                        b = bord(len(self.bords), ed.index, fa.index)
                    else :
                        faceunique = False
                        break
            if faceunique :
                self.bords.append(b)
        #calcul du contour
        ed = me.edges[self.bords[0].edgeindex]
        self.contour.append(ed.vertices[0])
        lastvert = ed.vertices[1]
        while lastvert != self.contour[0] :
            self.contour.append(lastvert)
            previousvert = self.contour[len(self.contour)-2]
            lv = set([lastvert])
            pv = set([previousvert])
            # on recherche le bord adjacent au bord défini par lastvert et previousvert
            for b in self.bords :
                ed = me.edges[b.edgeindex]
                e = set([ed.vertices[0],ed.vertices[1]])
                # le bord est adjacent s'il contient lastvert mais pas previousvert (sinon c'est le même bord !)
                if (lv == lv & e) and (e == e - pv) :
                    if ed.vertices[0]==lastvert :
                        lautrevert = ed.vertices[1]
                    else :
                        lautrevert = ed.vertices[0]
                    break
            lastvert = lautrevert

    def getBoundSquare(self, coefunit) :
        bb = self.blenderobject.bound_box
        lesX = [p[0] for p in bb]
        lesY = [p[1] for p in bb]
        xmin = min(lesX)*coefunit
        xmax = max(lesX)*coefunit
        ymin = min(lesY)*coefunit
        ymax = max(lesY)*coefunit
        return [[xmin, ymin], [xmax, ymax]]

    def export(self, svgfile, e, coefunit) :
        atts = {}
        atts["id"] = self.blenderobject.name
        a = xml.sax.xmlreader.AttributesImpl(atts)
        e.startElement("g", a)
        atts = {}
        atts["id"] = self.blenderobject.name+"_polys"
        a = xml.sax.xmlreader.AttributesImpl(atts)
        e.startElement("g", a)
        me = self.blenderobject.data
        for fa in me.polygons :
            atts = {}
            atts["class"] = "poly"
            atts["id"] = "poly" + str(fa.index)
            points = ""
            first = True
            for vei in fa.vertices : #vei = vertex index
                ve = me.vertices[vei]
                if not first : points += ","
                first = False
                points += str(ve.co.x*coefunit) + " " + str(ve.co.y*coefunit) 
            atts["points"] = points
            a = xml.sax.xmlreader.AttributesImpl(atts)
            e.startElement("polygon", a)
            e.endElement("polygon")
        e.endElement("g")

        atts = {}
        atts["class"] = "contour"
        atts["id"] = self.blenderobject.name+"_contour"
        a = xml.sax.xmlreader.AttributesImpl(atts)
        me = self.blenderobject.data
        points = ""
        first = True
        for vei in self.contour :
            ve = me.vertices[vei]
            if not first : points += ","
            first = False
            points += str(ve.co.x*coefunit) + " " + str(ve.co.y*coefunit) 
        atts["points"] = points
        a = xml.sax.xmlreader.AttributesImpl(atts)
        e.startElement("polygon", a)
        e.endElement("polygon")

        atts = {}
        atts["id"] = self.blenderobject.name+"_numeros"
        a = xml.sax.xmlreader.AttributesImpl(atts)
        e.startElement("g", a)
        for b in self.bords :
            ed = me.edges[b.edgeindex]
            v1i = ed.vertices[0]
            v2i = ed.vertices[1]
            v1 = me.vertices[v1i]
            v2 = me.vertices[v2i]
            atts = {}
            atts["class"] = "numedge"
            atts["id"] = "poly" + str(ed.index)
            cx = (v1.co.x+v2.co.x)*coefunit/2
            cy = (v1.co.y+v2.co.y)*coefunit/2
            atts["x"] = str(cx)
            atts["y"] = str(cy)
            #calcul de la rotation à appliquer au numéro pour qu'il suive le bord en étant à l'intérieur de l'ilot
            fa = me.polygons[b.faceindex]
            for vei in fa.vertices : 
                if (vei != v1i) and (vei != v2i) : v3i = vei
            v3 = me.vertices[v3i]
            vecv1 = Vector(v1.co)
            vecv2 = Vector(v2.co)
            vecv3 = Vector(v3.co)
            vecx = Vector([1,0,0])
            vec1 = vecv2-vecv1
            vec2 = vecv3-vecv1
            angle = vecx.angle(vec1)
            cv = vecx.cross(vec1)
            if cv.z < 0 : angle = -angle
            cv = vec1.cross(vec2)
            if cv.z > 0 : angle = angle + pi
            angle = degrees(angle)
            atts["transform"] = "rotate("+str(angle)+", "+str(cx)+", "+str(cy)+")"
            e.startElement("text", atts)
            svgfile.write(str(self.edges_srcindexes[ed.index]))
            e.endElement("text")
        e.endElement("g")
        e.endElement("g")

##################################################################################################
# Au fur et à mesure du processus, le mesh source va etre découpé en ilots de faces dévelopables #
##################################################################################################
faces_to_unfold = [poly.index for poly in mesh_to_unfold.polygons] 
# plutôt que [i for i in range(len(mesh_to_unfold.polygons))] qui fonctionnait par chance 
# parce que les index des faces sont consécutifs et commencent à zéro comme  les index des listes
# cette liste sert à mémoriser les index des faces qui restent à traiter
# pour commencer cette liste contient les index de toutes les faces du mesh source
# Au fur et à mesure du traitement, on supprimera les index des faces qui ont été traitées
# Ce décompte est utile lorsqu'on ne peut pas déplier le mesh en un seul morceau (ilot)
islands = [] #on enregistrera chaque nouvel ilot créé dans cette liste

while (len(faces_to_unfold) > 0) :      

    island_verts = [] #liste destiné à mémoriser l'index des vertice dans le mesh source et ses nouvelles coordonnées après transformation sous la forme [[srcindex, [x, y, z]], .....]
    island_faces = [] #liste d'objets de class face_relationships
    island_completed = False

    while (not island_completed) :
        # si on n'a encore traité aucune face, on prend la première de la liste pour commencer un nouvel ilot   
        if (island_faces == []) :
            index_face_to_unfold = faces_to_unfold[0]
            candidate_face_rel = face_relationships(index_face_to_unfold, None)
        # sinon, on examine la dernière des faces traitées
        else :
            last_unfolded_face_relationships = island_faces[-1]
            # si cette dernière face traitée n'a pas de face parente (elle est donc également la première)
            # alors on va rechercher ses faces adjacentes
            if (last_unfolded_face_relationships.parentface_relationships == None) :
                face_to_explore_rel = last_unfolded_face_relationships
            # sinon on va d'abord terminer l'exploration de la face parente
            # (ie s'assurer qu'on a exploré toutes ses faces adjacentes)
            else :
                face_to_explore_rel = last_unfolded_face_relationships.parentface_relationships
            # Maintenant qu'on sait à partir de quelle face poursuivre l'exploration du mesh,
            # on cherche la prochaine face qu'on pourrait tenter de déplier 
            index_face_to_unfold = None 
            while (index_face_to_unfold == None) and (island_completed == False) :
                index_face_to_unfold = face_to_explore_rel.FindAdjacent() 
                # s'il ne reste plus de face adjacente non explorée
                # alors on va explorer la face suivante dans la liste des faces dépliées
                # et ainsi de suite jusqu'à trouver une face candidate au déploiment
                # ou bien jusqu'à arriver au bout de la liste des faces dépliées
                # auquel cas, il n'est plus possible d'agrandir l'ilot en construction
                if (index_face_to_unfold == None) :
                    if (face_to_explore_rel.destfaceindex + 1 < len(island_faces)) :
                        face_to_explore_rel = island_faces[face_to_explore_rel.destfaceindex+1]
                    else :
                        island_completed = True
            if island_completed : break         
            candidate_face_rel = face_relationships(index_face_to_unfold, face_to_explore_rel)
        candidate_face = mesh_to_unfold.polygons[candidate_face_rel.srcfaceindex]
        if (candidate_face_rel.IsAdmited()) :
            candidate_face_rel.add_to_island_faces(island_faces)
            candidate_face_rel.add_to_island_verts(island_verts)
            faces_to_unfold.remove(candidate_face_rel.srcfaceindex)
            print("faces to unfold = ", faces_to_unfold)
            
            
    #construction de l'objet qui va recevoir l'ilot 
    faces = [frel.destfacevertsindexes for frel in island_faces]
    print(faces)
    coords = [v[1] for v in island_verts]
    me = bpy.data.meshes.new('myMesh')          # create a new mesh

    # Fill the mesh with verts, edges, faces 
    me.from_pydata(coords,[],faces)   # edges or faces should be [], or you ask for problems
    me.update(calc_edges=True)    # Update mesh with new data

    # on va faire la liste des index dans le mesh source des arêtes de l'ilot.
    # cette liste sera utile pour numéroter les arrêtes des ilots
    # Si on numerote les arêtes des ilots sur l'export svg avec leur index dans l'ilot
    # il sera impossible de voir la correspondance entre 2 arêtes de 2 ilots différents
    # ayant la même arête source dans le mesh
    # c'est pourquoi pour chaque arête de chaque ilôt, 
    # on va rechercher l'index de son arête correspondante dans le mesh source
    island_edges_src_indexes = []
    for edest in me.edges :
        v1destindex = edest.vertices[0] # l'un des vertice de l'arête courante
        v1srcindex = island_verts[v1destindex][0] # l'indice du vertex correspondant dans le mesh source
        v2destindex = edest.vertices[1] # l'autre vertex de l'arête courante
        v2srcindex = island_verts[v2destindex][0] # l'indice du vertex correspondant dans le mesh source
        for esrc in mesh_to_unfold.edges :
            if (v1srcindex in esrc.vertices) and (v2srcindex in esrc.vertices) : 
                island_edges_src_indexes.append(esrc.index) # Pour que ça fonctionne, on suppose que la boucle traite les arêtes dans l'ordre des index, sinon, il faudrait faire un dictionnaire...
    print(len(island_edges_src_indexes), " edges : ", island_edges_src_indexes)

    ob = bpy.data.objects.new("myObj", me)          # create an object with that mesh
    ob.location = bpy.context.scene.cursor_location   # position object at 3d-cursor
    bpy.context.scene.objects.link(ob)                # Link object to scene    
    isl = island(ob, island_edges_src_indexes)
    islands.append(isl)
 
print([len(isl.edges_srcindexes) for isl in islands])

#--------------------------------
# 2eme partie - export SVG
#--------------------------------

def exportSVG(filename) :
    global islands
    coefcm = 35.43307 # pour transformer les unite blender en cm plutôt qu'en px
    coefunit = coefcm # unité choisie le cm
    trait = 1/coefcm # epaisseur de trait calculé en prévision de la transformation
    print("filename = ", filename)
    svgfile = open(filename,"w")
    e = xml.sax.saxutils.XMLGenerator(svgfile, "UTF-8")
    atts = {}
    atts["width"] = "100%"
    atts["height"] = "100%"
    # calcul de la viewbox
    xminlist = []
    yminlist = []
    xmaxlist = []
    ymaxlist = []
    for isl in islands :
        bs = isl.getBoundSquare(coefunit)
        xminlist.append(bs[0][0])
        yminlist.append(bs[0][1])
        xmaxlist.append(bs[1][0])
        ymaxlist.append(bs[1][1])
    xmin = min(xminlist)
    ymin = min(yminlist)
    xmax = max(xmaxlist)
    ymax = max(ymaxlist)
    atts["viewBox"] = str(xmin)+" "+str(ymin)+" " +str(xmax-xmin)+" "+str(ymax-ymin)
    atts["xmlns:dc"] = "http://purl.org/dc/elements/1.1/"
    atts["xmlns:cc"] = "http://creativecommons.org/ns#"
    atts["xmlns:rdf"] = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
    atts["xmlns"] = "http://www.w3.org/2000/svg"
    atts["xmlns:sodipodi"] = "http://sodipodi.sourceforge.net/DTD/sodipodi-0.dtd"
    atts["xmlns:inkscape"] = "http://www.inkscape.org/namespaces/inkscape"
    e.startDocument()
    e.startElement("svg", atts)
    atts = {}
    atts["inkscape:document-units"] = "cm"
    e.startElement("sodipodi:namedview", atts)
    e.endElement("sodipodi:namedview")
    atts = {}
    atts["document-units"] = "cm"
    e.startElement("namedview", atts)
    e.endElement("namedview")
    e.startElement("defs", xml.sax.xmlreader.AttributesImpl({}))
    atts = {}
    atts["type"] = "text/css"
    atts["id"] = "MonStyle"
    e.startElement("style", atts)
    svgfile.write("polygon.poly{fill:rgb(255,255,255);stroke:rgb(50,50,50);stroke-width: 0.2pt}")
    svgfile.write("polygon.contour{fill:none;stroke:black;stroke-width: 1pt}")
    svgfile.write("text.numedge{font-size:8pt;font-style:normal;font-weight:normal;text-align:center;line-height:125%;writing-mode:lr-tb;text-anchor:middle;fill:#000000;fill-opacity:1;stroke:none;font-family:Bitstream Vera Sans}")
    e.endElement("style")
    e.endElement("defs")
    for isl in islands : 
        isl.export(svgfile, e, coefunit)
    e.endElement("svg")
        
#filename = objet_actif.name + ".svg"
#print(filename)
#Blender.Window.FileSelector(exportSVG, "choisir nom de fichier", filename)

class exportToSVG(bpy.types.Operator):
    bl_idname = "export.export_to_svg"
    bl_label = "Export To SVG"
    
    filepath = bpy.props.StringProperty(subtype="FILE_PATH")
    
    def execute(self, context):
        print(self.bl_label)
        print("nom de fichier choisi : ", self.filepath)
        exportSVG(self.filepath)
        return {"FINISHED"}
    
    def invoke(self, context, event):
        context.window_manager.fileselect_add(self)
        return {"RUNNING_MODAL"}

bpy.utils.register_class(exportToSVG)

# test call
bpy.ops.export.export_to_svg('INVOKE_DEFAULT')    