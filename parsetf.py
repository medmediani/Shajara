#!/usr/bin/env python
# -*- coding: utf-8 -*-
import sys,os
import codecs,re
from optparse import OptionParser
from operator import itemgetter
from pygraphviz import *
from itertools import cycle
from collections import deque
import dot2tex as d2t
import subprocess

jalala=u"الله"
fonts={
       "trad":["\\texttrad","Traditional Arabic"],  
       "tradb":["\\texttradb", "Traditional Arabic Bold"],
      "simpl":["\\textsimpl", "Simplified Arabic"],
       "simplb":["\\textsimplb", "Simplified Arabic Bold"],
      "cour":["\\textcour", "Courier"],
      "courbd":["\\textcourbd", "Courier Bold"],
      "arial":["\\textarial", "Arial (Times)"],
      "arialbd":["\\textarialbd", "Arial (Times) Bold"],
      "andalus":["\\textandalus", "Andalus"],
      "thol":["\\textthol", "Tholoth"],
       "yerm":["\\textyerm", "Yermook"],
       "mash":["\\textmash", "Mashq"],
      "hor":["\\texthor", "Hor"],
       "battar":["\\textbattar", "Battar"],
      "granada":["\\textgranada", "Granada"],
      "kayrawan":["\\textkayrawan", "Kayrawan"],
       "dimnah":["\\textdimnah", "Dimnah"],
       "sindibad":["\\textsindibad", "Sindibad"],
       "graph":["\\textgraph", "Graph"],
      "nice":["\\textnice", "Nice"],
       "mohanad":["\\textmohanad", "Almohanad"],
      "mothnna":["\\textmothnna", "Almothnna"],
      "mateen":["\\textmateen", "Almateen"],
      "petra":["\\textpetra", "Petra"],
      "nada":["\\textnada", "Nada"],
       "cortoba":["\\textcortoba", "Cortoba"],
       "ostora":["\\textostora", "Ostorah"],
       "furat":["\\textfurat", "Furat"],
       "salem":["\\textsalem", "Salem"],
      "shado":["\\textshado", "Shado"],
       "metal":["\\textmetal", "Metal"],
      "tarablus":["\\texttarablus", "Tarablus"],
       "khalid":["\\textkhalid", "Khalid"],
      "sharjah":["\\textsharjah", "Sharjah"],
      "hani":["\\texthani", "Hani"],
      "ouhod":["\\textouhod", "Ouhod"],
      "rehan":["\\textrehan" ,  "Rehan"]
       }

fonts_desc=dict((des, [texcode, code]) for code, [texcode, des] in fonts.iteritems())
    
separator=";"
shapes=[
        "box", 
        "polygon", 
        "ellipse", 
        "circle", 
        "triangle", 
       "plaintext", 
       "diamond", 
       "trapezium", 
       "parallelogram", 
       "pentagon", 
       "hexagon", 
        "septagon", 
       "octagon", 
       "doublecircle", 
       "doubleoctagon", 
       "tripleoctagon", 
        "Mdiamond", 
        "Msquare", 
        "Mcircle", 
        "rect", 	
        "rectangle", 
        "square", 
        "none", 	
        "note", 
        "tab", 
        "folder", 
        "star"
    ]
compilers={
           "pdftex":"pdflatex", 
           "xetex":"xelatex", 
           "polyglo":"xelatex"
           }
ar_tex_cmds={
             "pdftex":r"\AR", 
             "xetex":r"\textarab[utf]", 
             "polyglo":r"\textarabic"
             }
             
preamble={
          "pdftex":"%%%%%%The following lines are inserted in order to support Arabi\n\\usepackage[english,arabic]{babel }\n\\usepackage[T1,LFE,LAE]{fontenc}\n\\usepackage{cmap}\n%%%%%%end of insertion\n", 
          "xetex":"%%%%%%The following lines are inserted in order to support ArabXeTeX\n\\usepackage{fontspec}\n\\usepackage{xltxtra}\n\\usepackage{arabxetex}\n\\usepackage{xunicode}\n\\usepackage{babel }\n\\usepackage{cmap}\n%%%%%end of insertion\n",
          "polyglo":"%%%%%%The following lines are inserted in order to support Polyglossia\n\\usepackage{bidi}\n\\usepackage{fontspec}\n\\usepackage{xltxtra,amsmath}\n\\usepackage{polyglossia}\n\\usepackage{cmap}\n\\setmainlanguage{english}\n\\setotherlanguage{arabic}%%%%%end of insertion\n"
          }
anchors={ 
             "TB":{"orig":".south", "dest":".north"}, 
             "BT":{"dest":".south", "orig":".north"}, 
             "LR":{"orig":".east", "dest":".west"}, 
             "RL":{"orig":".west", "dest":".east"}
             }
normalizers={
            ord(u"ـ"):None,  # remove tatweel
            ord(u"أ"):u"ا", 
            ord(u"إ"):u"ا", 
           ord( u"آ"):u"ا", 
            ord(u"\u0671"):u"ا", #wasla
           ord( u"\u0627"):u"ا",# bare 'alif
            ord( u"\u0670"):u"ا", # dagger 'alif
            ord(u"ؤ"):u"و", 
            #remove harakat
           ord(u"\u064B"): None, # fatHatayn
            ord(u"\u064C"): None, # Dammatayn
           ord( u"\u064D"): None, # kasratayn
            ord(u"\u064E"): None, # fatHa
            ord(u"\u064F"): None, # Damma
            ord(u"\u0650"): None, # kasra
            ord(u"\u0651"): None, # shaddah
            ord(u"\u0652"): None, # sukuun  
             }
nameof=itemgetter(0)
is_special=itemgetter(1)
parentof=itemgetter(2)

codeof=itemgetter(0)
descriptionof=itemgetter(1)

node_line=re.compile(r"^\s*\\node", re.U)
node_line_pgf=re.compile(r"^\s*\\draw\s*\(.*?\)\s*node\s*\{.+?\};$", re.U)
repl_id=re.compile(r"(?<=\{)'?(ID (\d+))(\$\\backslash\$nID (\d+))*'?(?=\};$)")
arc_line=re.compile(r"(^\s*\\draw.*?\()(.*?)(\).*?\()(.*?)(\);$)")

#re.compile(r"(?<=\{)'?(ID (\d+))'?(?=\};$)")
name_cleaner=re.compile(r"^\d*([\D]+)\d*$", re.U)
id_getter=re.compile(r"\d+")
special=re.compile(r"^([\s\*\-]*)([^\*\-]+)([\s\*\-]*)", re.U)
spaces=re.compile(r"\s+", re.U)
rep_spaces=re.compile(r"(\s)\1+", re.U)

class Node(object):
    def __init__(self,  name="",name_pos=0,  sp=False,  lines=[],parent=-1):
        self.__name=name
        self.__sp=sp
        self.__lines=lines
        self.__parent=parent
        self.__pos=name_pos
        self.__style=""
        self.__mainfont=""
        self.__extrafont=""
        self.__shape=""
        self.__id=-1
    @property
    def name(self):
        return self.__name
    @property
    def is_special(self):
        return self.__sp
    @is_special.setter
    def is_special(self, newsp):
        self.__sp=newsp
    
    @property
    def shape(self):
        return self.__shape
    @shape.setter
    def shape(self, ns):
        self.__shape=ns
        
    @property
    def style(self):
        return self.__style
    @style.setter
    def style(self, ns):
        self.__style=ns
    @property
    def main_font(self):
        return self.__mainfont
    @main_font.setter
    def main_font(self, nf):
        self.__mainfont=nf
    @property
    def extra_font(self):
        return self.__extrafont
    @extra_font.setter
    def extra_font(self, nf):
        self.__extrafont=nf
    @property
    def idstr(self):
        return ("ID %0"+str(len(self.__name))+"d")%self.__id
#    @idstr.setter
#    def idstr(self, nstr):
#        self.__idstr=nstr
    @property
    def lines(self):
        return self.__lines
    @property
    def id(self):
        return self.__id
    @id.setter
    def id(self, nid):
        self.__id=nid
    @property
    def parent(self):
        return self.__parent
    @parent.setter
    def parent(self, newp):
        self.__parent=newp
    @property
    def name_pos(self):
        return self.__pos  
    
    def anscestors(self, ids):
        yield self.__id
        if self.__parent>=0:
            yield self.__parent
            for anscestor in ids[self.__parent].anscestors(ids):
                yield anscestor
                
    def as_fake_str(self, id=0):
#        print self.__lines
        return "\n".join([self.idstr for line in self.__lines ])
        
    def __str__(self):
        return repr("{Name: '%s', Special: %s, Parent: %d, Lines: %s}" % (self.__name, "Yes" if self.__sp else "No", self.__parent, self.__lines))
    def __repr__(self):
        return str(self)
    def __nonzero__(self):
        return bool(self.__name)

class Token(object):
    def __init__(self, tok_str="", pos=0, sp=False, m=False):
        self.__str=tok_str
        self.__pos=pos
        self.__sp=sp
        self.__m=m
    @property
    def str(self):
        return self.__str
    @property
    def pos(self):
        return self.__pos
#    @pos.setter
#    def pos(self, newpos):
#        self.__pos=newpos
    @property
    def is_special(self):
        return self.__sp
#    @is_special.setter
#    def is_special(self, newsp):
#        self.__sp=newsp
    @property
    def is_main(self):
        return self.__m
#    @is_main.setter
#    def is_main(self, newm):
#        self.__m=newm
def font_like(font, fonts):
#    print "Looking for:", font
#    print "Looking in:", fonts
    if font:
        try:
            return (ft for ft in fonts if ft.lower()==font.lower()).next()
        except StopIteration:
            try:
                return (ft for ft in fonts if ft.lower().find(font.lower())>=0).next()
            except StopIteration:
                try:
                    return (ft for ft in fonts if font.lower().find(ft.lower())>=0).next()
                except StopIteration:
                    pass
    return font

def preprocess_line(line):
#    for c in line:
#        print c, ":", hex(ord(c)), "\t", 
    line=rep_spaces.sub(r"\1", line)
    return line
def norm_line(line):
    return line.translate(normalizers)

def available_arabic_fonts():
    #Unix specific
    p=subprocess.Popen("fc-list :lang=ar family", shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    
    out, err=p.communicate()
    if p.returncode:
        return []
    return  [x.split(",",1)[0] for x in out.replace("\\",",").split("\n")]
 
def norm_font(font):
    try:
        return descriptionof(fonts_desc[font])
    except KeyError:
        return font

def refine_font_name(font):
    font=font.replace("_", "")
    return font
def refine_code(code_lines, tex="pdftex", font="", sp_fonts=[]):
    code_lines[0]="\\documentclass[12pt,english]{article}"
    
    if not font:
        font="Scheherazade"
#    f_str=""
    if tex in ["xetex", "polyglo"] :
        f_str="\\newfontfamily\\arabicfont[Script=Arabic, Scale=1]{%s}\n" %font
#        for ft in enumerate(sp_fonts):
        f_str+="\n".join(["\\newfontfamily%s[Script=Arabic,Scale=1]{%s}\n" %(codeof(fonts[ft]), ft) for ft in sp_fonts])
#        code_lines.insert(1,f_str )
    preamble_updated=False
    for i, line in enumerate(code_lines):
        if line.startswith("\\usepackage") and line.endswith("{preview}"):
            code_lines[i]=preamble[tex]+(code_lines[i] if tex=="pdftex" else  (f_str+"\\usepackage[xetex,active,tightpage]{preview}"))
            preamble_updated=True
        if line==r"\begin{document}":
            if not preamble_updated:
                code_lines[i]=preamble[tex]+ (f_str if tex in["xetex", "polyglo"] else "")+code_lines[i]
            if tex=="pdftex":
                code_lines[i]+="\n\\selectlanguage{english}"
            break
        if tex in ["xetex", "polyglo"] and line==r"\usepackage[utf8]{inputenc}":
            code_lines[i]="%"+code_lines[i]
                
            
#    code_lines.insert(1,preamble[tex] )
    return code_lines

def refine_name(name, tex="pdftex", clean_name=False):
    if clean_name:
#        print "cleaning"
        name=name_cleaner.sub(r"\1", name).strip()
    if tex=="pdftex":
        name=name.replace(jalala, "\\allah")
    return  name
    
def replacer(ids_dic,tex="pdftex", clean_name=False): #,  font="", sp_fonts=[]):
    #csp_f=cycle(sp_fonts)
    def rep_ids(s):
        id=int(s.group(2))
        is_multi=len(ids_dic[id].lines)>1
        font=ids_dic[id].main_font
#        if sp_fonts and ids_dic[id].is_special:
#            return (r"\begin{tabular}{ c} " if is_multi else "")+"\\\\".join([" %s{%s{%s}} " % (ar_tex_cmds[tex], codeof(fonts[csp_f.next()]),refine_name(line, tex)) if pos==ids_dic[id].name_pos else " %s{\\tiny %s} " % (ar_tex_cmds[tex], refine_name(line, tex)) for pos, line in enumerate(ids_dic[id].lines)])+(" \end{tabular}" if is_multi else "")
        if font :#and # tex=="pdftex":
            return (r"\begin{tabular}{ c} " if is_multi else "")+"\\\\".join([" %s{%s{%s}} " % (ar_tex_cmds[tex], codeof(fonts[font]), refine_name(line, tex, clean_name)) if pos==ids_dic[id].name_pos else " %s{\\tiny %s} " % (ar_tex_cmds[tex],refine_name(line, tex)) for pos, line in enumerate(ids_dic[id].lines)] )+(" \end{tabular}" if is_multi else "")#ids_dic[int(s.group(2))].name)
        return  (r"\begin{tabular}{ c} " if is_multi else "")+"\\\\".join([" %s{%s} " % (ar_tex_cmds[tex], refine_name(line, tex, clean_name)) if pos==ids_dic[id].name_pos else " %s{\\tiny %s} " % (ar_tex_cmds[tex],refine_name(line, tex)) for pos, line in enumerate(ids_dic[id].lines)] )+(" \end{tabular}" if is_multi else "")#ids_dic[int(s.group(2))].name
    return rep_ids
        

def preproc_name(name_pos):    
    pos, name=name_pos
#    print "Name:", name
    m=special.match(name)
    if m:
#        print name ,"is special"
#        print "name=%s\tgroup 0=%s\tgroup 1=%s\tgroup 2= %s\tgroup 3=%s" % (name, m.group(0), m.group(1), m.group(2),  m.group(3))
#        print "special=", bool(spaces.sub("", m.group(1)+m.group(3)))
        sides=spaces.sub("", m.group(1)+m.group(3))
#        print "Name to return:", m.group(2)
        return Token(m.group(2), pos, sides.find("*")>=0,sides.find("-")>=0 )#, [m.group(2)]
    return Token(name,pos) #False, False, [name]

def seg_name(name_str):
#    print "name str:", name_str
    tokens=map(preproc_name, enumerate(filter(None, name_str.split(":") ) ))
#    print "Tokens:", 
#    for token in tokens:
#        print token.str, 
    try:
        mtok=(token for token in tokens if token.is_main).next()
    except StopIteration:
        mtok=tokens[0]
#    print "Tokens=", tokens
    return Node(mtok.str.strip(), mtok.pos, mtok.is_special, [token.str for token in tokens]) #itemgetter(0, 1, 3)(reduce(aggregate_names, tokens) )#[1:], tokens[0]+( [], ) ))
    
def generate_tree(f, order="fifo", normalize=False):
    cur_id=0
    forward={}
    ids={}
    for line in f:
#        print "Line before preproc:", line
#        print "Line after preproc:", preprocess_line(line)
        line=preprocess_line(line)
        if normalize:
            line=norm_line(line)
#        line=preproc_line(line)
        names=filter(None, map(lambda x: x.strip(), line.strip().split(".") )) #[x.strip() for x in line.strip().split(".") if x]
        if not names:
            continue
#        print "Names:", 
#        for name in names:
#            print name, 
        nodes=map(seg_name, names)#names[0], sp=seg_name()#preproc_name(names[0])
#        print "Nodes:", 
#        for node in nodes:
#            print node.name,
#        print "Nodes=", nodes
        if cur_id==0:
            ids[0]=nodes[0] #names[0], sp, -
            parent=0
        else:
#            print "parents with this name:", forward[nodes[0].name]
            try:
                ######
                ### refer to the last name mentioned if same name mentioned many times
                if order== 'fifo':
                    parent=forward[nodes[0].name].popleft()#names[0]][0]
                    #forward[names[0]]=forward[names[0]][1:]
                #######
                ## if want to refer to the first most name
                elif order=='lifo':
                    parent=forward[nodes[0].name].pop()
#                n, osp, p=ids[parent]
                ids[parent].is_special=ids[parent].is_special or nodes[0].is_special #sp or osp, p
            except (IndexError, KeyError):
                print >>sys.stderr,"Unexpected parent name: '%s'." % names[0]
                exit(1)
#        print "parent=", parent, ":", ids[parent].name
        for node in nodes[1:]:
            cur_id+=1
            node.parent=parent
#            print "cleaning", name
#            name, sp=preproc_name(name)
#            print "parent of ", name, "is", parent, ":", nameof(ids[parent]), "sp=", sp
            ids[cur_id]=node #name, sp, parent
#            print  "the new entry:", ids[cur_id]
            try:
                forward[node.name].append(cur_id)
            except KeyError:
                forward[node.name]=deque([cur_id])
    for id in ids:
        ids[id].id=id
#    edges=[(ids[node.parent].idstr,ids[cid].idstr) for cid,  node in ids.iteritems() if node.parent>=0]
    return  ids
        
def conv_labels(gr, ids):
    cnvd=gr.copy()
    for n in cnvd.iternodes():
        #print n
        m=id_getter.search(n)
        n.attr["label"]= repr(ids[int(m.group(0))].as_fake_str(int(m.group(0)))) if m else n #conv_label(n)
    return cnvd

#
def fix_anchors(code, dir,  fix_orig, fix_dest):
    if not (fix_orig or fix_dest):
#        print "returning"
        return code
     
    fixed=r"\1\2"+(anchors[dir]["orig"] if fix_orig else "")+r"\3\4"+(anchors[dir]["dest"] if fix_dest else "")+r"\5"
    return map(lambda line: arc_line.sub(fixed, line), code)
    
def min_segments(paths):
    segs=[]
    for path in paths:
#        print "Checking Path:", path
#        print "Current segments:", segs
        newsegs=[]
        for seg in segs:            
            newsegs.extend(filter(None, [seg &path, seg-path]))
            path-=seg
            if not path:
                break
        if path:
            newsegs.append(path)
#        print "Segs so far:", newsegs
        segs=newsegs
    return segs
def get_special_paths(ids):
    sp_paths=[]
    for id in ids:
        if ids[id].is_special:
            new_path=set(ids[id].anscestors(ids))
#            print "New path:", new_path
            sp_paths.append(new_path)
#            print "sp_paths before:", sp_paths
            for i, path in enumerate(sp_paths[:-1]):
                if sp_paths[-1] <=path:
#                    print "Path:", sp_paths[-1], "is contained in", path, "and will be deleted"
                    del sp_paths[-1]
                    break
                if path <=sp_paths[-1]:
#                    print "Path:", path, "is contained in", sp_paths[-1], "and will be deleted"
                    del sp_paths[i]
                    break
#            print "sp_paths after:", sp_paths
#    print "SPECIAL PATHS:", sp_paths
    return sp_paths
    
def set_node_attributes(ids, node_style,sp_styles, node_font, sp_fonts,  node_shape, sp_shapes, unify, texcomp):
#    if sp_styles:        
    styles=cycle(sp_styles)
    fonts=cycle(sp_fonts)
    sshapes=cycle(sp_shapes)
    
    if sp_styles or sp_fonts or sp_shapes:
        if unify:
            paths=get_special_paths(ids)
            #    print "Special paths:", paths
            sp_segs=min_segments(paths)
            for seg in sp_segs:
                style=""
                font=""
                shape=""
                if sp_fonts:
                    font=fonts.next()
                if sp_styles:
                    style=styles.next() 
                if sp_shapes:
                    shape=sshapes.next()
                for node in seg:
                    ids[node].style=style
#                    if texcomp=="pdftex":
                    ids[node].main_font=font
                    ids[node].shape=shape
        else:
            for id in ids:
                if ids[id].is_special:
                    if sp_styles:
                        ids[id].style=styles.next()
                    if sp_fonts:
                        ids[id].main_font=fonts.next()
                    if sp_shapes:
                         ids[id].shape=sshapes.next()
    
    for id in ids:
        if not ids[id].style:
            ids[id].style=node_style
        if not ids[id].main_font:
            if texcomp=="pdftex":
                ids[id].main_font=node_font
#        if not ids[id].extra_font:
        if texcomp=="pdftex":
            ids[id].extra_font=node_font  
        if not ids[id].shape:
            ids[id].shape=node_shape

def rep_ids(code, rep_func,  texfmt):
    return map(lambda line:repl_id.sub(rep_func, line)   if (texfmt=="tikz" and node_line.match(line)) or (texfmt=="pgf" and node_line_pgf.match(line)) else line, code)

def main():
    global fonts
    description="This program parses an Arabic text file in order to build a family genealogical tree.\nThe file is analysed line by line, "\
                        "every line is expected to expand a parent (at the first position) together with his children separated by periods '.'. "\
                        "If everything works fine, the tree is saved as a figure in pdf format and consequently can be  inserted later in other documents "\
                        "or printed directly. Since the structure is hierarchical, every parent name (except the first) should have been previously mentioned. "\
                        "In order to highlight (a) special path(s) in the tree, the special names should be marked with (an) asterisk(s) '*' at the beginning "\
                        "and/or at the end of that special name. For special names you can specify particular styles and/or particular fonts."\
                        "Every name can be preceded/followed by small comments by separating them by ':'. In such case, the order will be respected, "\
                        "and the main name should be marked with '-' sign(s) at one/both of its sides if it is not the first.'-' and '*' sign(s) can be safely mixed. "\
                        "Three typesetting systems are supported at the moment, namely: 'Arabi', 'ArabXeTeX', and 'Polyglossia'. Arabi is simpler and supports less fonts. "\
                        "With ArabXeTeX or Polyglossia you can use any of your installed fonts, but you need a new version of the 'Preview' package. "\
                        "Please report any feedback to Mohammed Mediani: medmediani@hotmail.com "
    usage = "Usage: %prog [options] tree-source-file"
    parser = OptionParser(usage)
    parser.set_description(description)
    parser.add_option("-s", "--style", action="store",type="string",
                      dest="style",
                      help="{straight|square} straight: default style, straight connectors,\rsquare: squared connectors",
                      default="straight")
    parser.add_option("-o", "--order", action="store",type="string",
                      dest="order",
                      help="{fifo|lifo} fifo: the parent name refers to the last occurence of this name, lifo: the name refers to the earliest occurence, default: fifo",
                      default="fifo")
    parser.add_option("-f", "--font", action="store",type="string",
                      dest="font",
                      help="Select a specific font. supported fonts for 'pdftex' (in the format: 'code: font name'): {%s}. Available Arabic fonts for 'XeTeX'/'Polyglossia' (Unix only) {%s}" % ("|".join(" %s: %s " % (x, descriptionof(y)) for x, y in fonts.items()), "|".join(available_arabic_fonts())), 
                      default="")
    parser.add_option("-n", "--node-style", action="store",type="string",
                      dest="node_style",
                      help="String describing TikzStyle for the nodes (eg. 'fill=red!20', to get nodes filled with 20% of red). Enclose inside SINGLE quotes if contains spaces or special characters", 
                      default="")
    parser.add_option("-e", "--edge-style", action="store",type="string",
                      dest="edge_style",
                      help="String describing TikzStyle forthe edges (eg. '-diamond, blue' to get zigzagged green edges). Enclose inside SINGLE quotes if contains spaces or special characters", 
                      default="")
    parser.add_option("-N", "--special-node-styles", action="store",type="string",
                      dest="special_styles",
                      help="%s-seprated string of node styles for special nodes in order to highlight a particular path in the tree. The program will cycle through this list and assign styles accordingly to special names. Enclose inside SINGLE quotes if contains spaces or special characters" % separator, 
                      default="")
    parser.add_option("-F", "--special-fonts", action="store",type="string",
                      dest="special_fonts",
                      help="%s-seprated string of fonts for special nodes in order to highlight a particular path in the tree. The program will cycle through this list and assign fonts accordingly to special names. Enclose inside SINGLE quotes if contains spaces or special characters"% separator, 
                      default="")
    parser.add_option("-E", "--special-edge-styles", action="store",type="string",
                      dest="special_edge_styles",
                      help="%s-seprated string of edge styles for special paths in order to highlight a particular path in the tree. The program will cycle through this list and assign styles accordingly to special edges. Enclose inside SINGLE quotes if contains spaces or special characters"%separator, 
                      default="")
    parser.add_option("-d", "--dir", action="store",type="string",
                      dest="dir",
                      help="{BT|TB|LR|RL} direction if the tree. B: bottom, T: top, L: left, R: right", 
                      default="tb")
   
    parser.add_option("-x", "--texformat", action="store",type="string",
                      dest="tex_format",
                      help="{tikz|pgf} package used to generate the graph in Latex.", 
                      default="tikz")
    parser.add_option("-p", "--node-shape", action="store",type="string",
                      dest="node_shape",
                      help="The shape of nodes {%s}." % "|".join(shapes), 
                      default="box")
    parser.add_option("-P", "--special-node-shape", action="store",type="string",
                      dest="special_node_shapes",
                      help="%s-seprated string of shapes for special nodes. This would allow a node to be more visually attractive. The program will cycle through this list and assign shapes accordingly to special names. Enclose inside SINGLE quotes if contains spaces or special characters" % separator, 
                      default="")
                      
    parser.add_option("-c", "--tex-compiler", action="store",type="string",
                      dest="tex_compiler",
                      help="{pdftex|xetex|polyglo} TeX system. The Arabi typesetting system will be used for 'pdftex', the ArabXeTeX system will be used for 'xetex', and Polyglossia will be used for 'polyglo'", 
                      default="pdftex")
                      
    parser.add_option("-a", "--explicit-orig-anchor", action="store_true", 
                      help="Use this flag if the edges start points don't anchor correctly. This adds an explicit anchor in the TeX code.", 
                      dest="fix_orig") #, 
#                      default="False")
    parser.add_option("-b", "--explicit-dest-anchor", action="store_true", 
                       help="Use this flag if the edges ending points don't anchor correctly. This adds an explicit anchor in the TeX code.", 
                      dest="fix_dest")#, 
#                      default="False")
    parser.add_option("-l", "--explicit-node-anchor", action="store_true", 
                       help="Use this flag if the nodes in one level don't align correctly. This adds an explicit anchor in the TeX code.", 
                      dest="fix_alignments")#, 
    parser.add_option("-u", "--unify-special-paths", action="store_true", 
                       help="Use this flag in order to propagate the special styles for one node over all its anscestors. Intersecting special paths cause the style to be changed.", 
                      dest="unify_styles")#, 
    parser.add_option("-z", "--normalize", action="store_true", 
                       help="Use this flag to normalize the Arabic input text. For instance: all forms of 'Hamza' will be normalized to a single form, 'Tatweel' will be removed, any 'Tashkeel' will be removed, etc", 
                      dest="normalize")#, 
    parser.add_option("-i", "--use-indexes", action="store_true", 
                       help="In case many similar names occur in the tree and it becomes difficult to choose either 'fifo' or 'lifo', names can be numerically indexed by pre/suf-fixing them with digits to avoid conflicts. If this flag is used, the indexes will be automatically removed before writing the names out.", 
                      dest="use_indexes")
    (options, args) = parser.parse_args()
    
    
    if len(args) < 1:    
        parser.error("No tree source file given")
   
    sys.stdout = codecs.getwriter('utf8')(sys.stdout)   
    sys.stderr= codecs.getwriter('utf8')(sys.stderr)    
    pstyle=options.style.lower()
    if pstyle not in ["straight","square"]:
        parser.error("Unknown style '%s'"% pstyle)
    
    order=options.order.lower()
    if order not in ["fifo", "lifo"]:
        parser.error("Unknown order'%s'. Should belong to {fifo,lifo}"%(options.order))
    
    texcomp=options.tex_compiler.lower()
    if texcomp not in ["pdftex","xetex", "polyglo"]:
        parser.error("Unknown TeX system '%s'. Should belong to {pdftex,xetex,polyglo}"% options.tex_compiler)
    
    font=options.font
    font=font_like(font, fonts_desc.keys() if  texcomp=="pdftex" else available_arabic_fonts())
    if font and texcomp=="pdftex":
        font=norm_font(font).lower()
        if font not in fonts.keys():
            parser.error("Unknown font '%s'. Supported fonts are: %s"% (font, fonts.keys()))
    
    dir=options.dir.upper()
    if dir not in ["TB", "BT","LR", "RL"]:
        parser.error("Unknown direction'%s'. Should belong to {TB,BT,LR,RL}"% options.dir)
    texfmt=options.tex_format.lower()
    if texfmt not in ["tikz","pgf"]:
        parser.error("Unknown TeX format'%s'. Should belong to {tikz,pgf}"% options.tex_format)
    
    try:
        f=codecs.open(args[0],"r","utf8")
    except IOError:
        parser.error("Could not open file: '%s'"% args[0])
    
    print "Source file: '%s'\nOrder: '%s'\nStyle: %s" %(args[0], order, pstyle)
    if font:
        if texcomp=="pdftex":
            print "Font: %s" % descriptionof(fonts.get(font, font))
        else:
            print "Font:", font
    
    print "Direction: %s" % dir
    print "TeX format: %s" %texfmt
    print "TeX system: %s"%texcomp
    node_shape=options.node_shape.lower()
    if node_shape in ["mcircle", "msquare","mdiamond" ]:
        node_shape=node_shape.title()
    if node_shape not in shapes:
        parser.error("Unknown shape '%s'. Should belong to {%s}"% (options.node_shape, "|".join(shapes)))
    print "Shape of nodes: %s" %    node_shape
     
     
    node_style=options.node_style 
    if node_style:
        print "Node style=", node_style
    edge_style=options.edge_style #.replace(" ", "")
    if edge_style:
        print "Edge style=", edge_style
        
    special_shapes=map(lambda s:  s in ["mcircle", "msquare","mdiamond"] and s.title() or s, filter(None,options.special_node_shapes.lower().split(separator)))  or  []
    for nshape in special_shapes:
        if nshape not in shapes:
            parser.error("Unknown shape '%s'. Should belong to {%s}"% (nshape, "|".join(shapes)))
    if special_shapes:
        print "Special node shapes:", special_shapes
    special_styles=filter(None,options.special_styles.split(separator))  if options.special_styles else []
    if special_styles:
        print "Special node styles=", special_styles
        
    special_fonts=filter(None,options.special_fonts.split(separator)) if options.special_fonts else []
#    print "Special fonts before:", special_fonts
    if special_fonts:
#        for ft in special_fonts:
        special_fonts=[font_like(ft, fonts_desc.keys() if  texcomp=="pdftex" else available_arabic_fonts()) for ft in special_fonts]
        
        if texcomp=="pdftex":            
            special_fonts=[x.lower() for x in map(norm_font, special_fonts)]
            unknowns=filter(lambda x: x not in fonts.keys() ,  special_fonts)
            if unknowns: #ft not in fonts.keys():
                parser.error("Unknown special fonts %s.  Supported fonts are: %s"% (unknowns,  fonts.keys()))
        else:
            fonts=dict((ft, ["\\"+refine_font_name(spaces.sub("", ft)), ft]) for ft in special_fonts)
            
            
        print "Special node fonts=",[descriptionof(fonts[ft ]) for ft in special_fonts]
        
    special_edge_styles=filter(None,options.special_edge_styles.split(separator)  ) if options.special_edge_styles else []
    if special_edge_styles:
        print "Special edge styles=", special_edge_styles
        
    print "Explicit origin anchors:", ("yes" if options.fix_orig else "no")
    print "Explicit destination anchors:", ("yes" if options.fix_dest else "no")
    print "Explicit node alignment anchors:", ("yes" if options.fix_alignments else "no")
    print "Propagate special features over ancsestors:", ("yes" if options.unify_styles else "no")
    print "Normalize Arabic text:", ("yes" if options.normalize else "no")
    print "Using indexes in names:", (options.use_indexes and "yes" or "no")
    print
    print 
    
    
    g=AGraph(   strict=False,directed=True)
    print "Generating the tree..."
    ids=generate_tree(f, order, options.normalize)
    print "Tree generated\nGenerating TeX code..."
    
    anchor_style=",anchor="+anchors[dir]["dest"][1:]
    first_anchor_style=",anchor="+anchors[dir]["orig"][1:]

    set_node_attributes(ids, node_style, special_styles,font, special_fonts, node_shape, special_shapes, options.unify_styles ,  texcomp)

    for id in ids:
        style=""
        if options.fix_alignments and texfmt=="tikz":
            if id==0:
                style=first_anchor_style
            else:
                style=anchor_style
        g.add_node(ids[id].idstr, style=ids[id].style+style, shape=ids[id].shape)
    
    if special_edge_styles and options.unify_styles:
        sp_paths=get_special_paths(ids)
        sp_paths_edges=map(lambda path: set(zip(sorted(path), sorted(path)[1:])) , sp_paths)
#        print "sp_paths_edges:", sp_paths_edges
        
        sp_segs=min_segments(sp_paths_edges)
#        print "special segments:",  sp_segs
        segs_styles=zip(sp_segs, cycle(special_edge_styles))
#        print "segs_styles:", segs_styles
        sp_edges=set([])
        sp_edges.update(*sp_segs)
        
        edges=filter(lambda x: x not in sp_edges, [(ids[i].parent, i)  for i in ids if ids[i].parent>=0])
#        print "special edges:",  sp_edges
        for seg, style in segs_styles:
            g.add_edges_from([(ids[id0].idstr, ids[id1].idstr) for id0, id1 in seg], style=edge_style+","+style)
    else:
        edges=[(ids[i].parent, i)  for i in ids if ids[i].parent>=0]
        
        
   
    g.add_edges_from([(ids[id0].idstr, ids[id1].idstr) for (id0, id1) in edges], style=edge_style)    
    preamble=""
    path=""
    if pstyle=="square":
        if dir in ["TB", "BT"]:
            preamble=r"\usetikzlibrary{calc}\tikzstyle{fork vertical} =[to path={|- ($(\tikztostart)!0.3!(\tikztotarget)$) -| (\tikztotarget) \tikztonodes}]"
            path="fork vertical"
        else:
            preamble=r"\usetikzlibrary{calc}\tikzstyle{fork horizontal} =[to path={-| ($(\tikztostart)!0.3!(\tikztotarget)$) |- (\tikztotarget) \tikztonodes}]"
            path="fork horizontal"
    g.graph_attr.update( rankdir=dir,   ratio="compress", size="10,8",  d2tdocpreamble = preamble);
#d2tdocpreamble = "\\usepackage[T1,LFE,LAE]{fontenc}\n\\usepackage[english,arabic]{babel }\n")#r"\tikzstyle{every state}=[draw=blue!50,very thick,fill=red!20]")
    g.node_attr.update(  texmode='verbatim', shape=node_shape, style=node_style)
    g.edge_attr.update(lblstyle="auto",topath=path ,  style=edge_style)
    
    getname=replacer(ids,texcomp, options.use_indexes)#,  font,special_fonts )
    
    g=conv_labels(g, ids)
    texcode = d2t.dot2tex(g.string(),  prog="dot", autosize=True,  format=texfmt,usepdflatex=True, tikzedgelabels=False,crop=True, straightedges=True)
    print "Code generated\nPost-processing the code..."
    code_lines=texcode.split("\n")
    pline=""
#    ins1=False
#    ins2=False

    code_lines=rep_ids(code_lines, getname, texfmt)
    if texfmt=="tikz":
        code_lines=fix_anchors(code_lines,dir,  options.fix_orig,options.fix_dest )        
    code_lines=refine_code(code_lines, texcomp, font, special_fonts)
##    for i, line in enumerate(code_lines):
#        if not ins1 and not line.startswith(r"\usepackage") and pline.startswith(r"\usepackage"):
#            code_lines.insert(i, r"\usepackage[english,arabic]{babel }")
#            code_lines.insert(i, r"\usepackage[T1,LFE,LAE]{fontenc}")
#            code_lines.insert(i, r"\usepackage{cmap}")
#            ins1=True
#        if not ins2 and pline==r"\begin{document}":
#            code_lines.insert(i,r"\selectlanguage{english}")
#            ins2=True
##        if (texfmt=="tikz" and node_line.match(line)) or (texfmt=="pgf" and node_line_pgf.match(line)):
#            print line
#            print "Line before:", code_lines[i]
##            code_lines[i]=repl_id.sub(getname, line)
#            print "line after:", code_lines[i]
#        pline=line
    texfilename=args[0]+".tex"
    print "Code saved to: '%s'"% texfilename
    codecs.open(texfilename, "w", "utf8").write("\n".join(code_lines))
#    g.draw(args[0]+".eps", prog="dot")
    g.write(args[0]+".dot")
    print "Compiling TeX code"
    p=subprocess.Popen("%s -halt-on-error %s"%(compilers[texcomp], texfilename), shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err=p.communicate()
    
    if p.returncode:
        print >>sys.stderr,  "An error occured while compiling:%s\nHave a look into '%s.log' to find out more." % (err, args[0])
    else:
        print "Successfully compiled\nResult saved to: '%s'" % (args[0]+".pdf")
    p.wait()
    #    print "cropping command: ", "pdfcrop --%s %s %s"%(texcomp, args[0]+".tmp.pdf", args[0]+".pdf")
#    print "Cropping the figure"
#    p=subprocess.Popen("pdfcrop --%s %s %s"%(texcomp, args[0]+".tmp.pdf", args[0]+".pdf"), shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
#    out, err=p.communicate()   
#    if p.returncode:
#        print >>sys.stderr,  "An error occured while cropping the figure: %s" % err
#        exit(p.returncode)
#    else:
#        print "Cropped correctly"
#        
#    p.wait()
#    os.system("pdflatex -halt-on-error "+texfilename)
    #g.graph_attr.update(rankdir="LR")
    #for n in g.iternodes():
    #    n.attr["label"]=repr(n.attr["label"])[1:-1]
    
    


    
if __name__=="__main__":
    main()
