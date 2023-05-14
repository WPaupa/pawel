.PHONY: all clean

all: interpreter

interpreter: AbsPawel.hs LexPawel.hs MatchChecker.hs Inference.hs OpParser.hs Binder.hs Calc.hs ParPawel.hs interpreter.hs
	ghc --make interpreter.hs

clean:
	rm -f *.o *.hi interpreter