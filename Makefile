%.vo : %.v
	coqc $*.v

gen.vo : gen.v

ddP.vo : gen.vo ddP.v

List_lemmasP.vo : List_lemmasP.v

lntP.vo : List_lemmasP.vo lntP.v

swappedP.vo : ddP.vo swappedP.v

lntacs.vo : swappedP.vo lntP.vo lntacs.v

lntls.vo : lntacs.vo lntls.v

lntrs.vo : lntls.vo lntrs.v

lntmtacs.vo : lntrs.vo lntmtacs.v

lntbR.vo : lntmtacs.vo lntbR.v

lntb1L.vo : lntbR.vo lntb1L.v

lntb2L.vo : lntb1L.vo lntb2L.v 

lntkt_exch.vo : lntb1L.vo lntb2L.vo lntbR.vo lntkt_exch.v

lnt_weakening.vo : lntkt_exch.vo lnt_weakening.v

lnt_contraction.vo : lnt_weakening.vo lntkt_exch.vo swappedP.vo lnt_contraction.v



existsT.vo : existsT.v

genT.vo : gen.vo existsT.vo genT.v

ddT.vo : genT.vo ddT.v

List_lemmasT.vo : ddT.vo List_lemmasT.v

lntT.vo : List_lemmasT.vo lntT.v

swappedT.vo : existsT.vo swappedT.v

lntacsT.vo : swappedT.vo lntT.vo lntacsT.v

lntlsT.vo : lntacsT.vo lntlsT.v

lntrsT.vo : lntlsT.vo lntrsT.v

lntmtacsT.vo : lntrsT.vo lntmtacsT.v

lntbRT.vo : lntmtacsT.vo lntbRT.v

lntb1LT.vo : lntbRT.vo lntb1LT.v

lntb2LT.vo : lntb1LT.vo lntb2LT.v 

lntkt_exchT.vo : lntb1LT.vo lntb2LT.vo lntbRT.vo lntkt_exchT.v

lnt_weakeningT.vo : lntkt_exchT.vo lnt_weakeningT.v

lnt_contractionT.vo : lnt_weakeningT.vo lntkt_exchT.vo swappedT.vo lnt_contractionT.v

clean : 
	rm -rf  *.vo *.glob *.v~

clean_win : 
	del /f *.vo *.glob
