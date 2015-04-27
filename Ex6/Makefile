Ex6-4-Dis: Ex6-4-Dis.agda ANSIEscapes.hs HaskellSetup.hs Ex6-Setup.agda Ex6-1-Vec.agda Ex6-2-Box.agda Ex6-3-Cut.agda
	agda --compile --ghc-flag "-lncurses" Ex6-4-Dis.agda

go4: Ex6-4-Dis
	./Ex6-4-Dis

Ex6-4-Dis-Sol: Ex6-4-Dis-Sol.agda ANSIEscapes.hs HaskellSetup.hs Ex6-Setup.agda Ex6-1-Vec-Sol.agda Ex6-2-Box-Sol.agda Ex6-3-Cut-Sol.agda
	agda --compile --ghc-flag "-lncurses" Ex6-4-Dis-Sol.agda

go4sol: Ex6-4-Dis-Sol
	./Ex6-4-Dis-Sol

Ex6-5-App-Sol: Ex6-5-App-Sol.agda Ex6-4-Dis-Sol.agda ANSIEscapes.hs HaskellSetup.hs Ex6-Setup.agda Ex6-1-Vec-Sol.agda Ex6-2-Box-Sol.agda Ex6-3-Cut-Sol.agda Ex6-4-Dis-Sol.agda
	agda --compile --ghc-flag "-lncurses" Ex6-5-App-Sol.agda

go5sol: Ex6-5-App-Sol
	./Ex6-5-App-Sol

Ex6-5-App: Ex6-5-App.agda Ex6-4-Dis.agda ANSIEscapes.hs HaskellSetup.hs Ex6-Setup.agda Ex6-1-Vec.agda Ex6-2-Box.agda Ex6-3-Cut.agda Ex6-4-Dis.agda
	agda --compile --ghc-flag "-lncurses" Ex6-5-App.agda

go5: Ex6-5-App
	./Ex6-5-App
