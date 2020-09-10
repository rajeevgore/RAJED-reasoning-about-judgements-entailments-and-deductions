%.vo : %.v
	coqc $*.v

gen.vo : gen.v

ddP.vo : gen.vo ddP.v

List_lemmasP.vo : List_lemmasP.v

lntP.vo : List_lemmasP.vo lntP.v

swappedP.vo : ddP.vo swappedP.v

lntacsP.vo : swappedP.vo lntP.vo lntacsP.v

lntlsP.vo : lntacsP.vo lntlsP.v

lntrsP.vo : lntlsP.vo lntrsP.v

lntmtacsP.vo : lntrsP.vo lntmtacsP.v

lntbRP.vo : lntmtacsP.vo lntbRP.v

lntb1LP.vo : lntbRP.vo lntb1LP.v

lntb2LP.vo : lntb1LP.vo lntb2LP.v 

lntkt_exchP.vo : lntb1LP.vo lntb2LP.vo lntbRP.vo lntkt_exchP.v

lnt_weakeningP.vo : lntkt_exchP.vo lnt_weakeningP.v

lnt_contractionP.vo : lnt_weakeningP.vo lntkt_exchP.vo swappedP.vo lnt_contractionP.v

lnt_contraction_mrP.vo : lnt_contractionP.vo lnt_contraction_mrP.v

lnt_gen_initP.vo : lntkt_exchP.vo lnt_weakeningP.vo lnt_gen_initP.v


existsT.vo : existsT.v

genT.vo : gen.vo existsT.vo genT.v

ddT.vo : genT.vo ddT.v

dd_fc.vo : ddT.vo dd_fc.v

List_lemmasT.vo : ddT.vo List_lemmasT.v

lntT.vo : ddT.vo List_lemmasT.vo lntT.v

swappedT.vo : existsT.vo lntT.vo swappedT.v

lntacsT.vo : swappedT.vo lntT.vo lntacsT.v

lntlsT.vo : lntacsT.vo lntlsT.v

lntrsT.vo : lntlsT.vo lntrsT.v

lntmtacsT.vo : lntrsT.vo lntmtacsT.v

lntbRT.vo : lntmtacsT.vo lntbRT.v

lntb1LT.vo : lntbRT.vo lntb1LT.v

lntb2LT.vo : lntb1LT.vo lntb2LT.v 

lntkt_exchT.vo : lntb1LT.vo lntb2LT.vo lntbRT.vo lntkt_exchT.v

lnt_weakeningT.vo : lntkt_exchT.vo lnt_weakeningT.v

contractedT.vo : lntacsT.vo List_lemmasT.vo contractedT.v

structural_equivalence.vo : lntT.vo contractedT.vo List_lemmasT.vo structural_equivalence.v

merge.vo : structural_equivalence.vo merge.v

lnt_contractionT.vo : contractedT.vo lnt_weakeningT.vo lntkt_exchT.vo swappedT.vo lnt_contractionT.v

lnt_contraction_mrT.vo : merge.vo lnt_contractionT.vo lnt_contraction_mrT.v

lnt_gen_initT.vo : lntkt_exchT.vo lnt_weakeningT.vo lnt_gen_initT.v



clean : 
	rm -rf  *.vo *.glob *.v~

clean_win : 
	del /f *.vo *.glob
