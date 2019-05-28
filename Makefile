%.vo : %.v
	coqc $*.v

gen.vo : gen.v

dd.vo : gen.vo dd.v

List_lemmas.vo : dd.vo List_lemmas.v

lnt.vo : List_lemmas.vo lnt.v

lntacs.vo : lnt.vo lntacs.v

lntls.vo : lntacs.vo lntls.v

lntrs.vo : lntls.vo lntrs.v

lntmtacs.vo : lntrs.vo lntmtacs.v

lntbR.vo : lntmtacs.vo lntbR.v

lntb1L.vo : lntbR.vo lntb1L.v

lntb2L.vo : lntb1L.vo lntb2L.v 





clean : 
	rm -rf  *.vo *.glob

clean_win : 
	del /f *.vo *.glob
