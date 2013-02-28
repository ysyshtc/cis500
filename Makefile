all: *.v
	coqc SfLib.v Imp.v ImpParser.v

before: *.v
	coqc Basics.v Induction.v Lists.v Poly.v MoreCoq.v Prop.v MoreProp.v Logic.v MoreInd.v

clean:
	rm *.vo *.glob *~
