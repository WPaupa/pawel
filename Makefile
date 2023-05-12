.PHONY: all clean

all: Conn

Conn: AbsPawel.hs LexPawel.hs MatchChecker.hs Inference.hs OpParser.hs Binder.hs Calc.hs ParPawel.hs Conn.hs
	ghc --make Conn.hs

clean:
	rm -f *.o *.hi Conn