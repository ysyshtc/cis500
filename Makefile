all: *.v
	coqc Basics.v Induction.v Lists.v Poly.v MoreCoq.v Prop.v

clean:
	rm *.vo *.glob *~
