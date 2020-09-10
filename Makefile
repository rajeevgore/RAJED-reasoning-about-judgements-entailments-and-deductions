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
tense-lns/gen.vo \
tense-lns/existsT.vo \
tense-lns/genT.vo \
tense-lns/ddT.vo \
tense-lns/dd_fc.vo \
tense-lns/List_lemmasT.vo \
tense-lns/lntT.vo \
tense-lns/swappedT.vo \
tense-lns/lntacsT.vo 

ljt/ljt.vo: ljt/ljt.v tense-lns/swappedT.vo tense-lns/lntacsT.vo tense-lns/List_lemmasT.vo general/gstep.vo general/gen_seq.vo
ljt/ljt_inv.vo: ljt/ljt_inv.v ljt/ljt.vo
ljt/ljt_ctr.vo: ljt/ljt_ctr.v ljt/ljt_inv.vo
ljt/ljt_ca.vo: ljt/ljt_ca.v ljt/ljt_ctr.vo
ll/ll_camq.vo ll/ll_camq.glob ll/ll_camq.v.beautified: ll/ll_camq.v tense-lns/dd_fc.vo tense-lns/lntT.vo tense-lns/swappedT.vo tense-lns/lntacsT.vo tense-lns/List_lemmasT.vo ll/fmlsext.vo ll/lldefs.vo ll/ll_lems.vo ll/ll_exch.vo ll/ll_cam.vo
ll/ll_cam.vo ll/ll_cam.glob ll/ll_cam.v.beautified: ll/ll_cam.v tense-lns/dd_fc.vo tense-lns/lntT.vo tense-lns/swappedT.vo tense-lns/lntacsT.vo general/gstep.vo
ll/ll_ca.vo ll/ll_ca.glob ll/ll_ca.v.beautified: ll/ll_ca.v tense-lns/ddT.vo
ll/lldefs.vo ll/lldefs.glob ll/lldefs.v.beautified: ll/lldefs.v tense-lns/ddT.vo ll/fmlsext.vo general/gstep.vo
ll/ll_exch.vo ll/ll_exch.glob ll/ll_exch.v.beautified: ll/ll_exch.v tense-lns/ddT.vo tense-lns/lntT.vo tense-lns/swappedT.vo tense-lns/lntacsT.vo general/gstep.vo
ll/ll_lems.vo ll/ll_lems.glob ll/ll_lems.v.beautified: ll/ll_lems.v tense-lns/dd_fc.vo tense-lns/swappedT.vo tense-lns/lntacsT.vo general/gentree.vo
ll/ll.vo ll/ll.glob ll/ll.v.beautified: ll/ll.v tense-lns/ddT.vo tense-lns/swappedT.vo tense-lns/lntacsT.vo
ll/fmlsext.vo ll/fmlsext.glob ll/fmlsext.v.beautified: ll/fmlsext.v tense-lns/ddT.vo tense-lns/List_lemmasT.vo tense-lns/lntT.vo
modal/k4_ca.vo modal/k4_ca.glob modal/k4_ca.v.beautified: modal/k4_ca.v tense-lns/dd_fc.vo tense-lns/List_lemmasT.vo tense-lns/lntT.vo tense-lns/swappedT.vo tense-lns/lntacsT.vo general/gstep.vo general/gentree.vo modal/gen_ext.vo general/rtcT.vo modal/k4.vo modal/k4_exch.vo modal/k4_inv.vo modal/k4_ctr.vo
modal/k4_ctr.vo modal/k4_ctr.glob modal/k4_ctr.v.beautified: modal/k4_ctr.v tense-lns/ddT.vo tense-lns/List_lemmasT.vo tense-lns/lntT.vo tense-lns/swappedT.vo tense-lns/lntacsT.vo general/gstep.vo modal/gen_ext.vo general/rtcT.vo modal/k4.vo modal/k4_exch.vo modal/k4_inv.vo
modal/k4_exch.vo modal/k4_exch.glob modal/k4_exch.v.beautified: modal/k4_exch.v tense-lns/ddT.vo general/gstep.vo modal/gen_ext.vo general/rtcT.vo tense-lns/List_lemmasT.vo tense-lns/lntT.vo tense-lns/lntacsT.vo tense-lns/swappedT.vo modal/k4.vo
modal/k4_inv.vo modal/k4_inv.glob modal/k4_inv.v.beautified: modal/k4_inv.v tense-lns/ddT.vo tense-lns/List_lemmasT.vo tense-lns/lntT.vo tense-lns/swappedT.vo tense-lns/lntacsT.vo general/gstep.vo modal/gen_ext.vo general/rtcT.vo modal/k4.vo modal/k4_exch.vo
modal/k4.vo modal/k4.glob modal/k4.v.beautified: modal/k4.v tense-lns/ddT.vo general/gstep.vo modal/gen_ext.vo tense-lns/List_lemmasT.vo tense-lns/lntT.vo tense-lns/lntacsT.vo
modal/gen_ext.vo modal/gen_ext.glob modal/gen_ext.v.beautified: modal/gen_ext.v tense-lns/gen.vo tense-lns/genT.vo tense-lns/lntT.vo general/gen_seq.vo
general/gentree.vo general/gentree.glob general/gentree.v.beautified: general/gentree.v tense-lns/dd_fc.vo general/rtcT.vo general/gstep.vo
general/gstep.vo general/gstep.glob general/gstep.v.beautified: general/gstep.v tense-lns/dd_fc.vo general/rtcT.vo
general/rtcT.vo general/rtcT.glob general/rtcT.v.beautified: general/rtcT.v tense-lns/gen.vo tense-lns/genT.vo
tense-lns/gen.vo tense-lns/gen.glob tense-lns/gen.v.beautified: tense-lns/gen.v
tense-lns/existsT.vo tense-lns/existsT.glob tense-lns/existsT.v.beautified: tense-lns/existsT.v
tense-lns/genT.vo tense-lns/genT.glob tense-lns/genT.v.beautified: tense-lns/genT.v tense-lns/existsT.vo tense-lns/gen.vo
tense-lns/ddT.vo tense-lns/ddT.glob tense-lns/ddT.v.beautified: tense-lns/ddT.v tense-lns/genT.vo tense-lns/gen.vo
tense-lns/dd_fc.vo tense-lns/dd_fc.glob tense-lns/dd_fc.v.beautified: tense-lns/dd_fc.v tense-lns/ddT.vo
tense-lns/List_lemmasT.vo tense-lns/List_lemmasT.glob tense-lns/List_lemmasT.v.beautified: tense-lns/List_lemmasT.v tense-lns/existsT.vo tense-lns/genT.vo tense-lns/gen.vo
tense-lns/lntT.vo tense-lns/lntT.glob tense-lns/lntT.v.beautified: tense-lns/lntT.v tense-lns/ddT.vo tense-lns/List_lemmasT.vo tense-lns/existsT.vo
tense-lns/swappedT.vo tense-lns/swappedT.glob tense-lns/swappedT.v.beautified: tense-lns/swappedT.v tense-lns/existsT.vo tense-lns/lntT.vo tense-lns/gen.vo
tense-lns/lntacsT.vo tense-lns/lntacsT.glob tense-lns/lntacsT.v.beautified: tense-lns/lntacsT.v tense-lns/ddT.vo tense-lns/List_lemmasT.vo tense-lns/lntT.vo tense-lns/swappedT.vo
general/gen_seq.vo: general/gen_seq.v tense-lns/lntacsT.vo general/gstep.vo

%.vo : %.v
	#echo doing $*.v >>log
	#dirname $* >>log
	(cd `dirname $*` ; pwd >> log ; coqc `basename $*.v`) 
	#pwd >> log
	# coqc -Q general "" -Q ll "" -Q modal "" -Q tense-lns "" $*.v

