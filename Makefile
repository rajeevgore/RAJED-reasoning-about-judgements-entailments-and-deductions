all: \
ljt/ljt.vo \
ljt/ljt_inv.vo \
ljt/ljt_ctr.vo \
ljt/ljt_ca.vo \
ll/ll_camq.vo \
ll/ll_cam.vo \
ll/ll_ca.vo \
ll/lldefs.vo \
ll/ll_exch.vo \
ll/ll_lems.vo \
ll/ll.vo \
ll/fmlsext.vo \
modal/k4_ca.vo \
modal/k4_ctr.vo \
modal/k4_exch.vo \
modal/k4_inv.vo \
modal/k4.vo \
modal/gen_ext.vo \
general/gentree.vo \
general/gstep.vo \
general/rtcT.vo \
general/gen_seq.vo \
general/gen_tacs.vo \
general/gen.vo \
general/existsT.vo \
general/genT.vo \
general/ddT.vo \
general/dd_fc.vo \
general/List_lemmasT.vo \
tense-lns/lntT.vo \
general/swappedT.vo \
tense-lns/lntacsT.vo 

ljt/ljt.vo: ljt/ljt.v general/swappedT.vo tense-lns/lntacsT.vo general/List_lemmasT.vo general/gstep.vo general/gen_seq.vo
ljt/ljt_inv.vo: ljt/ljt_inv.v ljt/ljt.vo
ljt/ljt_ctr.vo: ljt/ljt_ctr.v ljt/ljt_inv.vo
ljt/ljt_ca.vo: ljt/ljt_ca.v ljt/ljt_ctr.vo
ll/ll_camq.vo ll/ll_camq.glob ll/ll_camq.v.beautified: ll/ll_camq.v general/dd_fc.vo tense-lns/lntT.vo general/swappedT.vo tense-lns/lntacsT.vo general/List_lemmasT.vo ll/fmlsext.vo ll/lldefs.vo ll/ll_lems.vo ll/ll_exch.vo ll/ll_cam.vo
ll/ll_cam.vo ll/ll_cam.glob ll/ll_cam.v.beautified: ll/ll_cam.v general/dd_fc.vo tense-lns/lntT.vo general/swappedT.vo tense-lns/lntacsT.vo general/gstep.vo
ll/ll_ca.vo ll/ll_ca.glob ll/ll_ca.v.beautified: ll/ll_ca.v general/ddT.vo
ll/lldefs.vo ll/lldefs.glob ll/lldefs.v.beautified: ll/lldefs.v general/ddT.vo ll/fmlsext.vo general/gstep.vo
ll/ll_exch.vo ll/ll_exch.glob ll/ll_exch.v.beautified: ll/ll_exch.v general/ddT.vo tense-lns/lntT.vo general/swappedT.vo tense-lns/lntacsT.vo general/gstep.vo
ll/ll_lems.vo ll/ll_lems.glob ll/ll_lems.v.beautified: ll/ll_lems.v general/dd_fc.vo general/swappedT.vo tense-lns/lntacsT.vo general/gentree.vo
ll/ll.vo ll/ll.glob ll/ll.v.beautified: ll/ll.v general/ddT.vo general/swappedT.vo tense-lns/lntacsT.vo
ll/fmlsext.vo ll/fmlsext.glob ll/fmlsext.v.beautified: ll/fmlsext.v general/ddT.vo general/List_lemmasT.vo tense-lns/lntT.vo
modal/k4_ca.vo modal/k4_ca.glob modal/k4_ca.v.beautified: modal/k4_ca.v general/dd_fc.vo general/List_lemmasT.vo tense-lns/lntT.vo general/swappedT.vo tense-lns/lntacsT.vo general/gstep.vo general/gentree.vo modal/gen_ext.vo general/rtcT.vo modal/k4.vo modal/k4_exch.vo modal/k4_inv.vo modal/k4_ctr.vo
modal/k4_ctr.vo modal/k4_ctr.glob modal/k4_ctr.v.beautified: modal/k4_ctr.v general/ddT.vo general/List_lemmasT.vo tense-lns/lntT.vo general/swappedT.vo tense-lns/lntacsT.vo general/gstep.vo modal/gen_ext.vo general/rtcT.vo modal/k4.vo modal/k4_exch.vo modal/k4_inv.vo
modal/k4_exch.vo modal/k4_exch.glob modal/k4_exch.v.beautified: modal/k4_exch.v general/ddT.vo general/gstep.vo modal/gen_ext.vo general/rtcT.vo general/List_lemmasT.vo tense-lns/lntT.vo tense-lns/lntacsT.vo general/swappedT.vo modal/k4.vo
modal/k4_inv.vo modal/k4_inv.glob modal/k4_inv.v.beautified: modal/k4_inv.v general/ddT.vo general/List_lemmasT.vo tense-lns/lntT.vo general/swappedT.vo tense-lns/lntacsT.vo general/gstep.vo modal/gen_ext.vo general/rtcT.vo modal/k4.vo modal/k4_exch.vo
modal/k4.vo modal/k4.glob modal/k4.v.beautified: modal/k4.v general/ddT.vo general/gstep.vo modal/gen_ext.vo general/List_lemmasT.vo tense-lns/lntT.vo tense-lns/lntacsT.vo
modal/gen_ext.vo modal/gen_ext.glob modal/gen_ext.v.beautified: modal/gen_ext.v general/gen.vo general/genT.vo tense-lns/lntT.vo general/gen_seq.vo
general/gentree.vo general/gentree.glob general/gentree.v.beautified: general/gentree.v general/dd_fc.vo general/rtcT.vo general/gstep.vo
general/gstep.vo general/gstep.glob general/gstep.v.beautified: general/gstep.v general/dd_fc.vo general/rtcT.vo
general/rtcT.vo general/rtcT.glob general/rtcT.v.beautified: general/rtcT.v general/gen.vo general/genT.vo
general/gen.vo general/gen.glob general/gen.v.beautified: general/gen.v
general/gen_tacs.vo general/gen_tacs.glob general/gen_tacs.v.beautified: general/gen_tacs.v general/List_lemmasT.vo
general/existsT.vo general/existsT.glob general/existsT.v.beautified: general/existsT.v
general/genT.vo general/genT.glob general/genT.v.beautified: general/genT.v general/existsT.vo general/gen.vo
general/ddT.vo general/ddT.glob general/ddT.v.beautified: general/ddT.v general/genT.vo general/gen.vo
general/dd_fc.vo general/dd_fc.glob general/dd_fc.v.beautified: general/dd_fc.v general/ddT.vo
general/List_lemmasT.vo general/List_lemmasT.glob general/List_lemmasT.v.beautified: general/List_lemmasT.v general/existsT.vo general/genT.vo general/gen.vo
tense-lns/lntT.vo tense-lns/lntT.glob tense-lns/lntT.v.beautified: tense-lns/lntT.v general/ddT.vo general/gen_tacs.vo general/existsT.vo
general/swappedT.vo general/swappedT.glob general/swappedT.v.beautified: general/swappedT.v general/existsT.vo tense-lns/lntT.vo general/gen.vo
tense-lns/lntacsT.vo tense-lns/lntacsT.glob tense-lns/lntacsT.v.beautified: tense-lns/lntacsT.v general/ddT.vo general/List_lemmasT.vo tense-lns/lntT.vo general/swappedT.vo
general/gen_seq.vo: general/gen_seq.v tense-lns/lntacsT.vo general/gstep.vo

%.vo : %.v
	#echo doing $*.v >>log
	#dirname $* >>log
	(cd `dirname $*` ; pwd >> log ; coqc `basename $*.v`) 
	#pwd >> log
	# coqc -Q general "" -Q ll "" -Q modal "" -Q tense-lns "" $*.v

