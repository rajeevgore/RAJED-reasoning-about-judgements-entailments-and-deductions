all: general modal ll ljt
ljt: \
ljt/ljt.vo \
ljt/ljt_inv.vo \
ljt/ljt_ctr.vo \
ljt/ljt_ca.vo \
ljt/ljt_dn.vo \
ljt/ljt_dncc.vo \
ljt/ljt_dnca.vo \
ljt/ljt_dnterm.vo 
ll: \
ll/ll_camq.vo \
ll/ll_cam.vo \
ll/ll_ca.vo \
ll/lldefs.vo \
ll/ll_exch.vo \
ll/ll_lems.vo \
ll/ll.vo \
ll/fmlsext.vo
modal: \
modal/k4_ca.vo \
modal/k4_ctr.vo \
modal/k4_exch.vo \
modal/k4_inv.vo \
modal/k4.vo \
modal/gen_ext.vo 
general: \
general/existsT.vo \
general/gentree.vo \
general/gstep.vo \
general/rtcT.vo \
general/gen_tacs.vo \
general/gen.vo \
general/genT.vo \
general/ddT.vo \
general/dd_fc.vo \
general/List_lemmasT.vo \
general/swappedT.vo \
general/gen_seq.vo 

ljt/ljt.vo: ljt/ljt.v general/swappedT.vo general/gstep.vo general/gen_seq.vo 
ljt/ljt_inv.vo: ljt/ljt_inv.v ljt/ljt.vo
ljt/ljt_ctr.vo: ljt/ljt_ctr.v ljt/ljt_inv.vo 
ljt/ljt_ca.vo: ljt/ljt_ca.v ljt/ljt_ctr.vo
ljt/ljt_dn.vo: ljt/ljt_dn.v ljt/ljt_inv.vo
ljt/ljt_dncc.vo: ljt/ljt_dncc.v ljt/ljt_dn.vo ljt/ljt_ca.vo
ljt/ljt_dnca.vo: ljt/ljt_dnca.v ljt/ljt_dncc.vo ljt/ljt_ca.vo
ljt/ljt_dnterm.vo: ljt/ljt_dnterm.v ljt/ljt.vo general/rtcT.vo general/gen_tacs.vo
ll/ll_camq.vo: ll/ll_camq.v general/dd_fc.vo ll/fmlsext.vo ll/lldefs.vo ll/ll_lems.vo ll/ll_exch.vo ll/ll_cam.vo
ll/ll_cam.vo: ll/ll_cam.v general/swappedT.vo general/gentree.vo
ll/ll_ca.vo: ll/ll_ca.v general/ddT.vo
ll/lldefs.vo: ll/lldefs.v ll/fmlsext.vo general/gstep.vo
ll/ll_exch.vo: ll/ll_exch.v general/swappedT.vo general/gstep.vo
ll/ll_lems.vo: ll/ll_lems.v general/swappedT.vo general/gentree.vo
ll/ll.vo: ll/ll.v general/ddT.vo general/swappedT.vo 
ll/fmlsext.vo: ll/fmlsext.v general/ddT.vo general/gen_tacs.vo general/List_lemmasT.vo 
modal/k4_ca.vo: modal/k4_ca.v general/gen_tacs.vo general/gen_seq.vo general/gentree.vo modal/k4_ctr.vo
modal/k4_ctr.vo: modal/k4_ctr.v general/gstep.vo modal/k4_inv.vo
modal/k4_inv.vo: modal/k4_inv.v modal/k4_exch.vo
modal/k4_exch.vo: modal/k4_exch.v general/swappedT.vo modal/k4.vo
modal/k4.vo: modal/k4.v general/gstep.vo modal/gen_ext.vo general/List_lemmasT.vo 
modal/gen_ext.vo: modal/gen_ext.v general/genT.vo general/gen_seq.vo
general/gentree.vo: general/gentree.v general/gstep.vo
general/gstep.vo: general/gstep.v general/dd_fc.vo general/rtcT.vo
general/rtcT.vo: general/rtcT.v general/genT.vo
general/gen.vo: general/gen.v
general/gen_tacs.vo: general/gen_tacs.v general/List_lemmasT.vo
general/existsT.vo: general/existsT.v
general/genT.vo: general/genT.v general/existsT.vo general/gen.vo
general/ddT.vo: general/ddT.v general/genT.vo 
general/dd_fc.vo: general/dd_fc.v general/ddT.vo
general/List_lemmasT.vo: general/List_lemmasT.v general/existsT.vo general/genT.vo general/gen.vo
general/swappedT.vo: general/swappedT.v general/gen_tacs.vo general/List_lemmasT.vo
general/gen_seq.vo: general/gen_seq.v general/gstep.vo general/swappedT.vo

%.vo : %.v
	#echo doing $*.v >>log
	#dirname $* >>log
	(cd `dirname $*` ; pwd >> log ; coqc `basename $*.v`) 
	#pwd >> log
	# coqc -Q general "" -Q ll "" -Q modal "" -Q tense-lns "" $*.v

clean : 
	rm -rf  *.vo *.glob

