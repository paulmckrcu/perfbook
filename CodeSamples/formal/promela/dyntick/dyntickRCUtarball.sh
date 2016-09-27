rm -rf dyntickRCU
mkdir dyntickRCU
cp	dyntickRCU-base-sl-busted.spin.trail.txt \
	dyntickRCU-base-s.spin \
	dyntickRCU-irq-ssl.spin \
	RCUpreemptStates.fig \
	dyntickRCU-irqnn-ssl.spin \
	dyntickRCU-irq-nmi-ssl.spin \
	runspin.sh \
	dyntickRCU-base-sl.spin \
	dyntickRCU-base-sl-busted.spin.trail \
	dyntickRCU-base-sl-busted.spin \
	RCUpreemptStates.png \
	dyntickRCU-base.spin \
	RCUpreemptStates.eps \
	dyntickRCU.$1.html \
	dyntickRCU
tar -czf dyntickRCU.$1.tgz dyntickRCU
