;  ---------------------------------------------------------------------------------
;  --- Modulo che effettua le inferenze basandosi sulle osservazioni disponibili ---
;  ---------------------------------------------------------------------------------
(defmodule AGENT_CELL_BASE_INFERENCE (import AGENT ?ALL) (export ?ALL))


;regola che scatta quando c'è una nuova cella con probabilità a zero
(defrule manage-water-g-cell (declare (salience 50))
	?gcell <- (g-cell (x ?x) (y ?y) (probability 0))
	?row <- (g-per-row (row ?x) (g-cells $?rows) (gk-cells $?gkrows))
	?col <- (g-per-col (col ?y) (g-cells $?cols) (gk-cells $?gkcols))
=>
	(printout t "Water cell [" ?x ", " ?y "]" crlf)
	(retract ?gcell)	
	(assert (k-cell (x ?x) (y ?y) (content water)))
	(modify ?row (g-cells (delete-member$ $?rows ?y)) (gk-cells (delete-member$ $?gkrows ?y)))
	(modify ?col (g-cells (delete-member$ $?cols ?x)) (gk-cells (delete-member$ $?gkcols ?x)))
)

;ogni volta che c'è una nuova k-cell, memorizzo le informazioni
; per la relativa g-cell
(defrule initialize-fired-g-cell-boat (declare (salience 50))
	(k-cell (x ?x) (y ?y) (content ?content&~water))
	?gcell <- (g-cell (x ?x) (y ?y) (content nil))
=>
	(modify ?gcell (probability 1) (content ?content))
)

;se ho trovato tutte le navi di grandezza ?size
; elimino tutte le combinazioni di gradezzia ?size, visto che non servono più
(defrule remove-boat-combinations-when-found (declare (salience 50))
     (found-all-boats ?size)
	 ?comb <- (comb-boat (size ?size))
	 =>
	 (retract ?comb)
)

;se non ho ancora trovato una barca da 4, genero tutte le combinazioni possibili
;sia per riga...
(defrule initialize-4-boat-combinations-row (declare (salience 40))
	(not (initialized-combinations))
	(not (found-all-boats 4))
	(g-per-row (row ?x) (gk-cells $? ?y ?yp1 ?yp2 ?yp3 $?) (num ?numCells))	
	(test (and (eq ?yp1 (+ ?y 1)) (eq ?yp2 (+ ?y 2)) (eq ?yp3 (+ ?y 3))))	
	(test (<= 4 ?numCells))
	=>
	(assert (comb-boat (size 4) (alignment hor) (mainColRow ?x) 
						(secColRow ?y ?yp1 ?yp2 ?yp3) 
						(initialSecColRow ?y ?yp1 ?yp2 ?yp3))
				)
)
; ...che per colonna
(defrule initialize-4-boat-combinations-col (declare (salience 40))
	(not (initialized-combinations))
	(not (found-all-boats 4))
	(g-per-col (col ?x) (gk-cells $? ?y ?yp1 ?yp2 ?yp3 $?) (num ?numCells))
	(test (and (eq ?yp1 (+ ?y 1)) (eq ?yp2 (+ ?y 2)) (eq ?yp3 (+ ?y 3))))	
	(test (<= 4 ?numCells))
	=>
	(assert (comb-boat (size 4) (alignment ver) (mainColRow ?x) 
						(secColRow ?y ?yp1 ?yp2 ?yp3) 
						(initialSecColRow ?y ?yp1 ?yp2 ?yp3))
				)
)

;inizializzazione delle combinazioni per le navi di grandezza 3
;sia per riga...
(defrule initialize-3-boat-combinations-row (declare (salience 40))
	(not (initialized-combinations))
	(not (found-all-boats 3))
	(g-per-row (row ?x) (gk-cells $? ?y ?yp1 ?yp2 $?) (num ?numCells))
	(test (and (eq ?yp1 (+ ?y 1)) (eq ?yp2 (+ ?y 2))))	
	(test (<= 3 ?numCells))
	=>
	(assert (comb-boat (size 3) (alignment hor) (mainColRow ?x) 
						(secColRow ?y ?yp1 ?yp2) 
						(initialSecColRow ?y ?yp1 ?yp2))
						)
)
; ...che per colonna
(defrule initialize-3-boat-combinations-col (declare (salience 40))
	(not (initialized-combinations))
	(not (found-all-boats 3))
	(g-per-col (col ?x) (gk-cells $? ?y ?yp1 ?yp2 $?) (num ?numCells))
	(test (and (eq ?yp1 (+ ?y 1)) (eq ?yp2 (+ ?y 2))))	
	(test (<= 3 ?numCells))
	=>
	(assert (comb-boat (size 3) (alignment ver) (mainColRow ?x) (secColRow ?y ?yp1 ?yp2) (initialSecColRow ?y ?yp1 ?yp2)))
)

;termina la fase di inizializzazione delle combinazioni
(defrule set-combination-initialization-done (declare (salience 39))
	=>
	(assert (initialized-combinations))
)


;;; INIZIO INFERENZE SULLE COMBINAZIONI DI NAVI ;;;
;se per una data combinazione una delle sue celle non esiste più,
;significa che contiene acqua e quindi la combinazione è inconsistente
; riga...
(defrule no-g-cell-for-combination-row (declare (salience 10))	
    ?comb <- (comb-boat (alignment hor) (mainColRow ?x) (secColRow $? ?y $?))
	(not (g-cell (x ?x) (y ?y)))
	=>
	(retract ?comb)
)
; ... colonna
(defrule no-g-cell-for-combination-col (declare (salience 10))	
    ?comb <- (comb-boat (alignment ver) (mainColRow ?y) (secColRow $? ?x $?))
	(not (g-cell (x ?x) (y ?y)))
	=>
	(retract ?comb)
)


;queste due regole devono avere una salience maggiore della regola update-candidate-g-cell-boat

;dato che per le combinazioni il multislot "secColRow" indica le celle per le 
;quali non si è certi contengano qualcosa, quando si è sicuri di avere qualcosa in una 
;cella della combinazione, si aggiorna il multislot rimuovendo la cella suddetta
; sia per colonna...
(defrule update-remaining-cells-for-combination-col (declare (salience 10))	
    (g-cell (x ?x) (y ?y) (probability 1))
	?comb <- (comb-boat (alignment ver) (mainColRow ?y) 
							(secColRow $?rows&:(member$ ?x $?rows)))	
	=>
	(modify ?comb (secColRow (delete-member$ $?rows ?x)))
)
; ... che per riga
(defrule update-remaining-cells-for-combination-row (declare (salience 10))	
    (g-cell (x ?x) (y ?y) (probability 1))
	?comb <- (comb-boat (alignment hor) (mainColRow ?x) 
							(secColRow $?cols&:(member$ ?y $?cols)))	
	=>
	(modify ?comb (secColRow (delete-member$ $?cols ?y)))
)

;le prossime due regole devono avere una salience maggiore delle regole inerenti le g-boat (navi)
;se trovo una nave, allora le combinazioni che contengono le celle della nave vengono scartate, perché inutili o inconsistenti
;quando nave e combinazione hanno lo stesso orientamento...
(defrule remove-combinations-for-boat-same (declare (salience 10))
	(g-boat (alignment ?alignment) (mainColRow ?x) (secColRow $? ?y $?))
	?comb <- (comb-boat (alignment ?alignment) (mainColRow ?x) 
							(initialSecColRow $?cols&:(member$ ?y $?cols)))	
=>	
	(retract ?comb)
)
; ... e quando hanno un orientamento ortogonale tra loro
(defrule remove-combinations-for-boat-orthogonal (declare (salience 10))
	(g-boat (alignment ?alignmentBoat) (mainColRow ?boatX) (secColRow $?boatCols))
	?comb <- (comb-boat (alignment ?alignmentComb&~?alignmentBoat) 
				(mainColRow ?combX) (initialSecColRow $?combCols)
			 )
	(and (member$ ?combX $?boatCols) (member$ ?boatX $?combCols))	
=>	
	(retract ?comb)
)

;rimuovo tutte quelle combinazioni che hanno un numero di celle maggiore delle celle 
;con delle navi per la relativa riga/colonna
;ad esempio se una colonna ha due celle con un pezzo di nave, ma la combinazione ma ne richiede tre, allora quella combinazione è inconsistente

; per riga...
(defrule remove-combination-row-not-enough-cells	
	?comb <- (comb-boat (alignment hor)	(mainColRow ?x) (secColRow $?cells))
	(g-per-row (row ?x) (num ?numCells))	
	(test (> (length$ $?cells) ?numCells))
=>	
	(retract ?comb)
)

;...per colonna
(defrule remove-combination-col-not-enough-cells	
	?comb <- (comb-boat (alignment ver)	(mainColRow ?y) (secColRow $?cells))
	(g-per-col (col ?y) (num ?numCells))	
	(test (> (length$ $?cells) ?numCells))
=>	
	(retract ?comb)
)

;rimuovo tutte le combinazioni che hanno nelle proprie vicinanze una cella sicura
;questo perché implica il fatto che esisterà una nave vicino alla combinazione, e quindi quest'ultima è inconsistente
;per colonna...
(defrule remove-combination-col-for-near-cells
	?comb <- (comb-boat (alignment ver)	(mainColRow ?y) (secColRow $?cells))
	(g-cell (probability 1) (y ?yCell&:(eq 1 (abs (- ?y ?yCell)))) (x ?xCell&:(member$ ?xCell $?cells)))
	=>
	(retract ?comb)
)

;...per riga
(defrule remove-combination-row-for-near-cells
	?comb <- (comb-boat (alignment hor)	(mainColRow ?x) (secColRow $?cells))
	(g-cell (probability 1)(x ?xCell&:(eq 1 (abs (- ?x ?xCell)))) (y ?yCell&:(member$ ?yCell $?cells)))
	=>
	(retract ?comb)
)

;funzione che indica se una cella è inclusa in una combinazione
(deffunction cell-in-comb
	(?xCell ?yCell ?combAlign ?combMainColRow ?combCells)
	(or (and (eq ?combAlign ver) (eq ?combMainColRow ?yCell) (member$ ?xCell $?combCells))
	    (and (eq ?combAlign hor) (eq ?combMainColRow ?xCell) (member$ ?yCell $?combCells)))
)

; se una cella è presente in tutte le combinazioni possibili per una data grandezza, 
; allora sicuramente conterrà una nave
; combinazioni da 4...
(defrule reveal-sure-cell-from-4-combinations (declare (salience -10))

	?gcell <- (g-cell (x ?x) (y ?y) (probability ~1))
	(comb-boat (size 4) (alignment ?alignment) (mainColRow ?mainColRow) (secColRow $?cells))
	(test (cell-in-comb ?x ?y ?alignment ?mainColRow $?cells))
	
	(forall ;questo predicato assicura che la cella sia presente in tutte le combinazioni
		(comb-boat (size 4) (alignment ?subAlignment) (mainColRow ?subMainColRow) (secColRow $?subCells))
		(test (cell-in-comb ?x ?y ?subAlignment ?subMainColRow $?subCells))
	)
	=>
	(modify ?gcell (probability 1))
)

; ... combinazioni da 3
(defrule reveal-sure-cell-from-3-combinations (declare (salience -10))

	?gcell <- (g-cell (x ?x) (y ?y) (probability ~1))
	(comb-boat (size 3) (alignment ?alignment) (mainColRow ?mainColRow) (secColRow $?cells))
	(test (cell-in-comb ?x ?y ?alignment ?mainColRow $?cells))
	
	(forall ;questo predicato assicura che la cella sia presente in tutte le combinazioni
		(comb-boat (size 3) (alignment ?subAlignment) (mainColRow ?subMainColRow) (secColRow $?subCells))
		(test (cell-in-comb ?x ?y ?subAlignment ?subMainColRow $?subCells))
	)
	=>
	(modify ?gcell (probability 1))
)

; se sono rimaste soltanto due combinazioni di grandezza 3, e non è stata trovata nessuna nave da 3,
; allora le due combinazioni conterranno le navi da 3
(defrule reveal-3-boat-from-unique-comb (declare (salience -10))
	(not (g-boat (size 3)))
	?boat1 <- (comb-boat (size 3) (alignment ?alignment1) (mainColRow ?mainColRow1) (secColRow $?cells1))
	?boat2 <- (comb-boat (size 3) (alignment ?alignment2) (mainColRow ?mainColRow2) (secColRow $?cells2))	
	(not (comb-boat (size 3)))
	=>
	(assert (g-boat (size 3) (alignment ?alignment1) (mainColRow ?mainColRow1) (secColRow $?cells1)))
	(assert (g-boat (size 3) (alignment ?alignment2) (mainColRow ?mainColRow2) (secColRow $?cells2)))
)


;;; FINE REGOLE INERENTI LE COMBINAZIONI ;;;


;;; INIZIO REGOLE INERENTI LE NAVI ;;;

;regole che servono per asserire quando sono state trovate tutte le navi di una certa dimensione
;grandezza 1 (4 navi)...
(defrule found-all-boats-1 (declare (salience 20))
	?boat1a <- (g-boat (size 1))
	?boat1b <- (g-boat (size 1))
	?boat1c <- (g-boat (size 1))
	?boat1d <- (g-boat (size 1))
	(test (and (< (fact-index ?boat1a) (fact-index ?boat1b)) 
			   (< (fact-index ?boat1b) (fact-index ?boat1c))
			   (< (fact-index ?boat1c) (fact-index ?boat1d))
			   ))
	=>
	(assert (found-all-boats 1))
)

;...grandezza 2 (3 navi)...
(defrule found-all-boats-2 (declare (salience 20))
	?boat2a <- (g-boat (size 2))
	?boat2b <- (g-boat (size 2))
	?boat2c <- (g-boat (size 2))
	(test (and (< (fact-index ?boat2a) (fact-index ?boat2b)) 
			   (< (fact-index ?boat2b) (fact-index ?boat2c))))
	=>
	(assert (found-all-boats 2))
)

;...grandezza 3 (2 navi)...
(defrule found-all-boats-3 (declare (salience 20))
	?boat3a <- (g-boat (size 3))
	?boat3b <- (g-boat (size 3))
	(test (< (fact-index ?boat3a) (fact-index ?boat3b)))
	=>
	(assert (found-all-boats 3))
)

;...grandezza 4 (1 nave)
(defrule found-all-boats-4 (declare (salience 20))
	(g-boat (size 4))
=>
	(assert (found-all-boats 4))
)


;se trovo una cella che contiene sub, allora ho trovato anche la relativa nave
(defrule find-boat-sub
	(g-cell (x ?x) (y ?y) (content sub))
=>	
	(assert (g-boat (size 1) (mainColRow ?x) (secColRow ?y) (alignment hor))) ;le navi sub hanno orientamento orizzontale
)

; se si trova una cella top e una bottom sulla stessa colonna e ad una distanza più o meno grande,
; si inferisce che esse appartengano ad una nave di via via maggiore grandezza
; navi verticali, grandezza 2...
(defrule find-boat-size-2-ver
	(g-cell (x ?x) (y ?y) (content top))
	(g-cell (x ?x2&:(eq ?x (- ?x2 1))) (y ?y) (content bot))
=>	
	(assert (g-boat (size 2) (mainColRow ?y) (secColRow ?x ?x2) (alignment ver)))
)

;...grandezza 3...
(defrule find-boat-size-3-ver
	(g-cell (x ?x) (y ?y) (content top))
	(g-cell (x ?x2&:(eq ?x (- ?x2 2))) (y ?y) (content bot))
=>	
	(bind ?x3 (+ ?x 1))
	(assert (g-boat (size 3) (mainColRow ?y) (secColRow ?x ?x3 ?x2) (alignment ver)))
)

;...grandezza 4
(defrule find-boat-size-4-ver
	(g-cell (x ?x) (y ?y) (content top))
	(g-cell (x ?x2&:(eq ?x (- ?x2 3))) (y ?y) (content bot))
=>	
	(bind ?x3 (+ ?x 1))
	(bind ?x4 (+ ?x 2))
	(assert (g-boat (size 4) (mainColRow ?y) (secColRow ?x ?x3 ?x4 ?x2) (alignment ver)))
)

;navi orizzontali grandezza 2...
(defrule find-boat-size-2-hor
	(g-cell (y ?y) (x ?x) (content left))
	(g-cell (y ?y2&:(eq ?y (- ?y2 1))) (x ?x) (content right))
=>	
	(assert (g-boat (size 2) (mainColRow ?x) (secColRow ?y ?y2) (alignment hor)))
)

;...grandezza 3...
(defrule find-boat-size-3-hor
	(g-cell (y ?y) (x ?x) (content left))
	(g-cell (y ?y2&:(eq ?y (- ?y2 2))) (x ?x) (content right))
=>	
	(bind ?y3 (+ ?y 1))
	(assert (g-boat (size 3) (mainColRow ?x) (secColRow ?y ?y3 ?y2) (alignment hor)))
)

;...grandezza 4
(defrule find-boat-size-4-hor
	(g-cell (y ?y) (x ?x) (content left))
	(g-cell (y ?y2&:(eq ?y (- ?y2 3))) (x ?x) (content right))
=>	
	(bind ?y3 (+ ?y 1))
	(bind ?y4 (+ ?y 2))
	(assert (g-boat (size 4) (mainColRow ?x) (secColRow ?y ?y3 ?y4 ?y2) (alignment hor)))
)

;se trovo 4 celle sicure tutte vicine, corrispondono sicuramente ad una nave da 4
;caso orizzontale...
(defrule find-boat-size-4-contiguous-cells-hor
	?gcellLeft <- (g-cell (y ?y1) (x ?x) (probability 1) (content ?c1))
	?gcellMiddle1 <- (g-cell (y ?y2&:(eq ?y1 (- ?y2 1))) (x ?x) (probability 1) (content ?c2))
	?gcellMiddle2 <- (g-cell (y ?y3&:(eq ?y1 (- ?y3 2))) (x ?x) (probability 1) (content ?c3))
	?gcellRight <- (g-cell (y ?y4&:(eq ?y1 (- ?y4 3))) (x ?x) (probability 1) (content ?c4))
	(test (or (eq ?c1 nil) 
			  (eq ?c2 nil)
			  (eq ?c3 nil)
			  (eq ?c4 nil)))
=>	
	(modify ?gcellLeft (content left))
	(modify ?gcellMiddle1 (content middle))
	(modify ?gcellMiddle2 (content middle))
	(modify ?gcellRight (content right))
	(assert (g-boat (size 4) (mainColRow ?x) (secColRow ?y1 ?y2 ?y3 ?y4) (alignment hor)))
)

;...caso verticale
(defrule find-boat-size-4-contiguous-cells-ver
	?gcellTop <- (g-cell (x ?x1) (y ?y) (probability 1) (content ?c1))
	?gcellMiddle1 <- (g-cell (x ?x2&:(eq ?x1 (- ?x2 1))) (y ?y) (probability 1) (content ?c2))
	?gcellMiddle2 <- (g-cell (x ?x3&:(eq ?x1 (- ?x3 2))) (y ?y) (probability 1) (content ?c3))
	?gcellBot <- (g-cell (x ?x4&:(eq ?x1 (- ?x4 3))) (y ?y) (probability 1) (content ?c4))
	(test (or (eq ?c1 nil) 
			  (eq ?c2 nil)
			  (eq ?c3 nil)
			  (eq ?c4 nil)))
=>	
	(modify ?gcellTop (content top))
	(modify ?gcellMiddle1 (content middle))
	(modify ?gcellMiddle2 (content middle))
	(modify ?gcellBot (content bot))
	(assert (g-boat (size 4) (mainColRow ?y) (secColRow ?x1 ?x2 ?x3 ?x4) (alignment ver)))
)

;se trovo 3 celle sicure tutte vicine e ho già trovato la nave da 4, allora corrispondono sicuramente ad una nave da 3
;caso orizzontale...
(defrule find-boat-size-3-contiguous-cells-hor
	(found-all-boats 4)

	?gcellLeft <- (g-cell (y ?y1) (x ?x) (probability 1) (content ?c1))
	?gcellMiddle1 <- (g-cell (y ?y2&:(eq ?y1 (- ?y2 1))) (x ?x) (probability 1) (content ?c2))
	?gcellRight <- (g-cell (y ?y3&:(eq ?y1 (- ?y3 2))) (x ?x) (probability 1) (content ?c3))
	(test (or (eq ?c1 nil) 
			  (eq ?c2 nil)
			  (eq ?c3 nil)))
=>	
	(modify ?gcellLeft (content left))
	(modify ?gcellMiddle1 (content middle))
	(modify ?gcellRight (content right))
	(assert (g-boat (size 3) (mainColRow ?x) (secColRow ?y1 ?y2 ?y3) (alignment hor)))
)

;...caso verticale
(defrule find-boat-size-3-contiguous-cells-ver
	(found-all-boats 4)

	?gcellTop <- (g-cell (x ?x1) (y ?y) (probability 1) (content ?c1))
	?gcellMiddle1 <- (g-cell (x ?x2&:(eq ?x1 (- ?x2 1))) (y ?y) (probability 1) (content ?c2))
	?gcellBot <- (g-cell (x ?x3&:(eq ?x1 (- ?x3 2))) (y ?y) (probability 1) (content ?c3))
	(test (or (eq ?c1 nil) 
			  (eq ?c2 nil)
			  (eq ?c3 nil)))
=>	
	(modify ?gcellTop (content top))
	(modify ?gcellMiddle1 (content middle))
	(modify ?gcellBot (content bot))
	(assert (g-boat (size 3) (mainColRow ?y) (secColRow ?x1 ?x2 ?x3) (alignment ver)))
)

;se trovo 2 celle sicure tutte vicine e ho già trovato le navi da 4 e 3, allora corrispondono sicuramente ad una nave da 2
;caso orizzontale...
(defrule find-boat-size-2-contiguous-cells-hor
	(found-all-boats 4)
	(found-all-boats 3)

	?gcellLeft <- (g-cell (y ?y1) (x ?x) (probability 1) (content ?c1))
	?gcellRight <- (g-cell (y ?y2&:(eq ?y1 (- ?y2 1))) (x ?x) (probability 1) (content ?c2))
	(test (or (eq ?c1 nil) 
			  (eq ?c2 nil)))
=>	
	(modify ?gcellLeft (content left))
	(modify ?gcellRight (content right))
	(assert (g-boat (size 2) (mainColRow ?x) (secColRow ?y1 ?y2) (alignment hor)))
)

;...caso verticale
(defrule find-boat-size-2-contiguous-cells-ver
	(found-all-boats 4)
	(found-all-boats 3)

	?gcellTop <- (g-cell (x ?x1) (y ?y) (probability 1) (content ?c1))
	?gcellBot <- (g-cell (x ?x2&:(eq ?x1 (- ?x2 1))) (y ?y) (probability 1) (content ?c2))
	(test (or (eq ?c1 nil) 
			  (eq ?c2 nil)))
=>	
	(modify ?gcellTop (content top))
	(modify ?gcellBot (content bot))
	(assert (g-boat (size 2) (mainColRow ?y) (secColRow ?x1 ?x2) (alignment ver)))
)

;se sono rimaste solo navi sub, allora tutte le celle sicure sono sub
(defrule find-boat-size-1
	(found-all-boats 4)
	(found-all-boats 3)
	(found-all-boats 2)

	?gcellSub <- (g-cell (y ?y) (x ?x) (probability 1) (content nil))
=>	
	(modify ?gcellSub (content sub))
	(assert (g-boat (size 1) (mainColRow ?x) (secColRow ?y) (alignment hor)))
)


;le regole seguenti provvedono a inferire nuove celle basandosi sul numero di navi trovate

;se ci sono 2 celle contigue ma le navi da 2 sono state tutte trovate, allora è almeno una nave da 3 e quindi asserisco una cella sicura
;caso orizzontale...
(defrule extend-2-boat-hor
	(found-all-boats 2)
	(g-cell (y ?y1) (x ?x) (probability 1) (content left|right))
	?gcellMiddle1 <- (g-cell (y ?y2&:(eq 1 (abs (- ?y1 ?y2)))) (x ?x) (probability 1) (content nil))
	?gcellExt <- (g-cell (y ?y3&:(eq 1 (abs (- ?y1 ?y3)))) (x ?x))	
=>	
	(modify ?gcellMiddle1 (content middle))
	(modify ?gcellExt (probability 1))
)

;...caso verticale
(defrule extend-2-boat-ver
	(found-all-boats 2)
	(g-cell (x ?x1) (y ?y) (probability 1) (content bot|top))
	?gcellMiddle1 <- (g-cell (x ?x2&:(eq 1 (abs (- ?x1 ?x2)))) (y ?y) (probability 1) (content nil))
	?gcellExt <- (g-cell (x ?x3&:(eq 1 (abs (- ?x1 ?x3)))) (y ?y))	
=>	
	(modify ?gcellMiddle1 (content middle))
	(modify ?gcellExt (probability 1))
)

;se ci sono 3 celle contigue ma le navi da 3 sono state tutte pescate, allora è una nave da 4
;estensione da sinistra...
(defrule extend-3-boat-from-left
	(found-all-boats 3)
	(g-cell (y ?y1) (x ?x) (probability 1) (content left))
	(g-cell (y ?y2&:(eq ?y1 (- ?y2 1))) (x ?x) (probability 1))
	?gcellMiddle2 <- (g-cell (y ?y3&:(eq ?y1 (- ?y3 2))) (x ?x) (probability 1) (content nil))
	?gcellExt <- (g-cell (y ?y4&:(eq ?y1 (- ?y4 3))) (x ?x))
=>	
	(modify ?gcellMiddle2 (content middle))
	(modify ?gcellExt (probability 1))
)

;...estensione da destra...
(defrule extend-3-boat-from-right
	(found-all-boats 3)
	(g-cell (y ?y1) (x ?x) (probability 1) (content right))
	(g-cell (y ?y2&:(eq ?y1 (+ ?y2 1))) (x ?x) (probability 1))
	?gcellMiddle2 <- (g-cell (y ?y3&:(eq ?y1 (+ ?y3 2))) (x ?x) (probability 1) (content nil))
	?gcellExt <- (g-cell (y ?y4&:(eq ?y1 (+ ?y4 3))) (x ?x))
=>	
	(modify ?gcellMiddle2 (content middle))
	(modify ?gcellExt (probability 1))
)

;...estensione da sopra...
(defrule extend-3-boat-from-top
	(found-all-boats 3)
	(g-cell (x ?x1) (y ?y) (probability 1) (content top))
	(g-cell (x ?x2&:(eq ?x1 (- ?x2 1))) (y ?y) (probability 1))
	?gcellMiddle2 <- (g-cell (x ?x3&:(eq ?x1 (- ?x3 2))) (y ?y) (probability 1) (content nil))
	?gcellExt <- (g-cell (x ?x4&:(eq ?x1 (- ?x4 3))) (y ?y))
=>	
	(modify ?gcellMiddle2 (content middle))
	(modify ?gcellExt (probability 1))
)

;...estensione da sotto
(defrule extend-3-boat-from-bot
	(found-all-boats 3)
	(g-cell (x ?x1) (y ?y) (probability 1) (content bot))
	(g-cell (x ?x2&:(eq ?x1 (+ ?x2 1))) (y ?y) (probability 1))
	?gcellMiddle2 <- (g-cell (x ?x3&:(eq ?x1 (+ ?x3 2))) (y ?y) (probability 1) (content nil))
	?gcellExt <- (g-cell (x ?x4&:(eq ?x1 (+ ?x4 3))) (y ?y))
=>	
	(modify ?gcellMiddle2 (content middle))
	(modify ?gcellExt (probability 1))
)


;quando si scopre una nuova nave, bisogna rimuovere dal multislot 'gk-cells' le relative celle
;questo perchè lo scopo di quel multislot e di tener traccia delle celle per le quali non si conosce che nave è presente
;caso orizzonale...
(defrule update-known-boat-hor
	(g-boat (alignment hor) (mainColRow ?x) (secColRow $? ?y $?))
	?row <- (g-per-row (row ?x) (gk-cells $?rows))
	?col <- (g-per-col (col ?y) (gk-cells $?cols))
	(test(and (member$ ?y $?rows) (member$ ?x $?cols)))
=>	
	(modify ?row (gk-cells (delete-member$ $?rows ?y)))
	(modify ?col (gk-cells (delete-member$ $?cols ?x)))
)

;...caso verticale
(defrule update-known-boat-ver
	(g-boat (alignment ver) (mainColRow ?y) (secColRow $? ?x $?))
	?row <- (g-per-row (row ?x) (gk-cells $?rows))
	?col <- (g-per-col (col ?y) (gk-cells $?cols))
	(test(and (member$ ?y $?rows) (member$ ?x $?cols)))
=>	
	(modify ?row (gk-cells (delete-member$ $?rows ?y)))
	(modify ?col (gk-cells (delete-member$ $?cols ?x)))
)

;rimozione delle celle troppo piccole per contenere una nave
;le tre regole seguenti si applicano a grandezze sempre maggiori
;caso in cui ho trovato tutte le navi da 1...
(defrule remove-g-cell-no-2-boat 
	(found-all-boats 1)
	?gcell <-(g-cell (x ?x) (y ?y) (content nil))

	(and (not (g-per-row (row ?x) (gk-cells $? ?ym1&:(- ?y 1) ?y $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?y ?yp1&:(+ ?y 1) $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm1&:(- ?x 1) ?x $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?x ?xp1&:(+ ?x 1) $?)))
	)
	=>
	(modify ?gcell (probability 0))
)

;...caso in cui ho trovato tutte le navi da 2...
(defrule remove-g-cell-no-3-boat 
	(found-all-boats 1)
	(found-all-boats 2)
	?gcell <-(g-cell (x ?x) (y ?y) (content nil))
	
	(and (not (g-per-row (row ?x) (gk-cells $? ?ym2&:(- ?y 2) ?ym1&:(- ?y 1) ?y $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?ym1&:(- ?y 1) ?y ?yp1&:(+ ?y 1) $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?y ?yp1&:(+ ?y 1) ?yp2&:(+ ?y 2) $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm2&:(- ?x 2) ?xm1&:(- ?x 1) ?x $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm1&:(- ?x 1) ?x ?xp1&:(+ ?x 1) $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?x ?xp1&:(+ ?x 1) ?xp2&:(+ ?x 2) $?)))
	)
	=>
	(modify ?gcell (probability 0))
)

;...caso in cui ho trovato tutte le navi da 3
(defrule remove-g-cell-no-4-boat 
	(found-all-boats 1)
	(found-all-boats 2)
	(found-all-boats 3)
	?gcell <-(g-cell (x ?x) (y ?y) (content nil))
	
	(and (not (g-per-row (row ?x) (gk-cells $? ?ym3&:(- ?y 3) ?ym2&:(- ?y 2) ?ym1&:(- ?y 1) ?y $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?ym2&:(- ?y 2) ?ym1&:(- ?y 1) ?y ?yp1&:(+ ?y 1) $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?ym1&:(- ?y 1) ?y ?yp1&:(+ ?y 1) ?yp2&:(+ ?y 2) $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?y ?yp1&:(+ ?y 1) ?yp2&:(+ ?y 2) ?yp3&:(+ ?y 3) $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm3&:(- ?x 3) ?xm2&:(- ?x 2) ?xm1&:(- ?x 1) ?x $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm2&:(- ?x 2) ?xm1&:(- ?x 1) ?x ?xp1&:(+ ?x 1) $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm1&:(- ?x 1) ?x ?xp1&:(+ ?x 1) ?xp2&:(+ ?x 2) $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?x ?xp1&:(+ ?x 1) ?xp2&:(+ ?x 2) ?xp3&:(+ ?x 3) $?)))
	)
	=>
	(modify ?gcell (probability 0))
)

;;; FINE INFERENZE BASATE SU NAVI


;;; INIZIO INFERENZE BASATE SULLE SINGOLE CELLE ;;;

; ogni volta che viene rilevata una g-cell sicura, aggiorno il conteggio delle celle rimanenti da trovare
; per righe e colonne
(defrule update-candidate-g-cells 
	(g-cell (x ?x) (y ?y) (probability 1))
	?row <- (g-per-row (row ?x) (num ?numRow) (g-cells $?rows))
	?col <- (g-per-col (col ?y) (num ?numCol) (g-cells $?cols))
	(test(and (member$ ?y $?rows) (member$ ?x $?cols)))
=>	
	(modify ?row (num (- ?numRow 1)) (g-cells (delete-member$ $?rows ?y)))
	(modify ?col (num (- ?numCol 1)) (g-cells (delete-member$ $?cols ?x)))
)


;se ci sono due celle vicine con probabilità 1, allora ciò che sta sopra o sotto (o a sinistra e destra) è acqua
;verticale...
(defrule water-for-contiguous-cells-hor
	(g-cell (x ?x) (y ?y) (probability 1))
	(g-cell (x ?x) (y ?y1&:(eq 1 (abs (- ?y ?y1)))) (probability 1))

	?gcell <- (g-cell (x ?xCell&:(eq 1 (abs (- ?x ?xCell)))) (y ?yCell))
	(or (test (>= 1 (abs (- ?y ?yCell)))) (test (>= 1 (abs (- ?y1 ?yCell)))))
	=>
	(modify ?gcell (probability 0))
)

;...orizzontale
(defrule water-for-contiguous-cells-ver
	(g-cell (y ?y) (x ?x) (probability 1))
	(g-cell (y ?y) (x ?x1&:(eq 1 (abs (- ?x ?x1)))) (probability 1))

	?gcell <- (g-cell (y ?yCell&:(eq 1 (abs (- ?y ?yCell)))) (x ?xCell))
	(or (test (>= 1 (abs (- ?x ?xCell)))) (test (>= 1 (abs (- ?x1 ?xCell)))))
	=>
	(modify ?gcell (probability 0))
)

;le celle che hanno acqua hanno probabilità 0 di avere una nave
(defrule set-probability-k-cell-water 
	?gcell <- (g-cell (x ?x) (y ?y))
	(k-cell (x ?x) (y ?y) (content water))
=>
	(modify ?gcell (probability 0))
)

;se il numero di celle contenenti altre navi per riga o colonna è arrivato a zero, rimuovo tutti i possibili candidati
; (bisogna escludere quelle celle per le quali la probabilità è certa)
;colonna...
(defrule remove-g-cell-col 
	(g-per-col (col ?y) (num 0))
	?gcell <- (g-cell (y ?y) (x ?x) (probability ~1))
	=>
	(modify ?gcell (probability 0))
)

;...riga
(defrule remove-g-cell-row 
	(g-per-row (row ?x) (num 0))
	?gcell <- (g-cell (x ?x) (y ?y) (probability ~1))
	=>
	(modify ?gcell (probability 0))
)

; tutte le celle vicine al sottomarino hanno probabilità zero
(defrule remove-g-cell-sub 
	(g-cell (x ?x) (y ?y) (content sub))
	?gcell <- (g-cell (x ?gx&:(<= (abs(- ?gx ?x)) 1)) (y ?gy&:(<= (abs(- ?gy ?y)) 1)))
	(test (or (neq ?gx ?x) (neq ?gy ?y)))
	=>
	(modify ?gcell (probability 0))
)

;inferenza sulla presenza di un sottomarino (qualora una cella con probabilità 1 ha intorno a sè soltanto acqua)
(defrule inference-g-cell-content-sub 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(and (not (g-cell (x ?x) (y ?y2&:(eq 1 (abs (- ?y ?y2))))))
	 	 (not (g-cell (x ?x2&:(eq 1 (abs (- ?x ?x2)))) (y ?y)))
	)
	=>
	(modify ?gcell (content sub))
)

;inferenza sulle celle con contenuto top, botton, left, right
;se ad esempio ho una cella sicura sotto ma non posso avere niente sopra, allora la cella è di tipo top
;caso top...
(defrule inference-g-cell-content-top 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (x ?x2&:(eq ?x2 (+ ?x 1))) (y ?y) (probability 1))
	(not (g-cell (x ?x3&:(eq ?x3 (- ?x 1))) (y ?y)))
	=>
	(modify ?gcell (content top))
)

;...caso bottom...
(defrule inference-g-cell-content-bot
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (x ?x2&:(eq ?x2 (- ?x 1))) (y ?y) (probability 1))
	(not (g-cell (x ?x3&:(eq ?x3 (+ ?x 1))) (y ?y)))
	=>
	(modify ?gcell (content bot))
)

;...caso left...
(defrule inference-g-cell-content-left 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (y ?y2&:(eq ?y2 (+ ?y 1))) (x ?x) (probability 1))
	(not (g-cell (y ?y3&:(eq ?y3 (- ?y 1))) (x ?x)))
	=>
	(modify ?gcell (content left))
)

;...caso right
(defrule inference-g-cell-content-right 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (y ?y2&:(eq ?y2 (- ?y 1))) (x ?x) (probability 1))
	(not (g-cell (y ?y3&:(eq ?y3 (+ ?y 1))) (x ?x)))
	=>
	(modify ?gcell (content right))
)

;rilevamento delle celle middle
;se ci sono celle sicure sopra e sotto (o a destra e sinistra) allora in contenuto della cella è middle
;caso orizzontale...
(defrule inference-g-cell-middle-hor
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (y ?y2&:(eq ?y2 (- ?y 1))) (x ?x) (probability 1))
	(g-cell (y ?y3&:(eq ?y3 (+ ?y 1))) (x ?x) (probability 1))
	=>
	(modify ?gcell (content middle))
)

;...caso verticale
(defrule inference-g-cell-middle-ver 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (x ?x2&:(eq ?x2 (- ?x 1))) (y ?y) (probability 1))
	(g-cell (x ?x3&:(eq ?x3 (+ ?x 1))) (y ?y) (probability 1))
	=>
	(modify ?gcell (content middle))
)

;quando si conosce il contenuto di una cella, è possibile conoscere quali celle avranno dell'acqua
;questo perché una nave non può essere vicina ad un'altra nave
;caso top...
(defrule remove-g-cell-for-top 
	(g-cell (x ?x) (y ?y) (content top))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?x ?gx) 1))
		     (test (eq ?gy ?y)))
		(and (test (<= (abs (- ?gx ?x)) 1))
		     (test (eq (abs (- ?gy ?y)) 1)))
		(and (test (eq (- ?gx ?x) 2))
		     (test (eq (abs (- ?gy ?y)) 1)))
	)
	=>
	(modify ?gcell (probability 0))
)

;...caso bottom...
(defrule remove-g-cell-for-bot
	(g-cell (x ?x) (y ?y) (content bot))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?gx ?x) 1))
		     (test (eq ?gy ?y)))
		(and (test (<= (abs (- ?gx ?x)) 1))
		     (test (eq (abs (- ?gy ?y)) 1)))
		(and (test (eq (- ?x ?gx) 2))
		     (test (eq (abs (- ?gy ?y)) 1)))
	)
	=>
	(modify ?gcell (probability 0))
)

;...caso left...
(defrule remove-g-cell-for-left 
	(g-cell (x ?x) (y ?y) (content left))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?y ?gy) 1))
		     (test (eq ?gx ?x)))
		(and (test (<= (abs (- ?gy ?y)) 1))
		     (test (eq (abs (- ?gx ?x)) 1)))
		(and (test (eq (- ?gy ?y) 2))
		     (test (eq (abs (- ?gx ?x)) 1)))
	)
	=>
	(modify ?gcell (probability 0))
)

;...caso right
(defrule remove-g-cell-for-right
	(g-cell (x ?x) (y ?y) (content right))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?gy ?y) 1))
		     (test (eq ?gx ?x)))
		(and (test (<= (abs (- ?y ?gy)) 1))
		     (test (eq (abs (- ?gx ?x)) 1)))
		(and (test (eq (- ?y ?gy) 2))
		     (test (eq (abs (- ?gx ?x)) 1)))
	)
	=>
	(modify ?gcell (probability 0))
)

;quando si conosce il contenuto di una cella, è possibile inferire sulle celle che sicuramente avranno qualcosa
;caso top...
(defrule inference-g-cell-from-top 
	(g-cell (x ?x) (y ?y) (content top))
	?gcellSure <- (g-cell (x ?x2&:(eq (- ?x2 1) ?x)) (y ?y) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
)

;...caso bottom...
(defrule inference-g-cell-from-bottom
	(g-cell (x ?x) (y ?y) (content bot))
	?gcellSure <- (g-cell (x ?x2&:(eq (- ?x 1) ?x2)) (y ?y) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
)

;...caso left...
(defrule inference-g-cell-from-left 
	(g-cell (x ?x) (y ?y) (content left))
	?gcellSure <- (g-cell (x ?x) (y ?y2&:(eq (- ?y2 1) ?y)) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
)

;...caso right
(defrule inference-g-cell-from-right 
	(g-cell (x ?x) (y ?y) (content right))
	?gcellSure <- (g-cell (x ?x) (y ?y2&:(eq (- ?y 1) ?y2)) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
)


;per una cella middle non si conosce il possibile orientamento, però se la cella ha qualcosa vicino a se è possibile 
;determinare il verso della nave e quindi inferire altre celle sicure
;caso top...
(defrule g-cell-continue-middle-from-top 
	(g-cell (x ?x) (y ?y) (content middle))
	(g-cell (x ?x2&:(eq (- ?x ?x2) 1)) (y ?y) (probability 1))
	?gcellSure <- (g-cell (x ?x3&:(eq (- ?x3 ?x) 1)) (y ?y) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
)

;...caso bottom...
(defrule g-cell-continue-middle-from-bottom
	(g-cell (x ?x) (y ?y) (content middle))
	(g-cell (x ?x2&:(eq (- ?x2 ?x) 1)) (y ?y) (probability 1))
	?gcellSure <- (g-cell (x ?x3&:(eq (- ?x ?x3) 1)) (y ?y) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
)

;...caso left...
(defrule g-cell-continue-middle-from-left 
	(g-cell (x ?x) (y ?y) (content middle))
	(g-cell (x ?x) (y ?y2&:(eq (- ?y ?y2) 1)) (probability 1))
	?gcellSure <- (g-cell (x ?x) (y ?y3&:(eq (- ?y3 ?y) 1)) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
)

;...caso right
(defrule g-cell-continue-middle-from-right 
	(g-cell (x ?x) (y ?y) (content middle))
	(g-cell (x ?x) (y ?y2&:(eq (- ?y2 ?y) 1)) (probability 1))
	?gcellSure <- (g-cell (x ?x) (y ?y3&:(eq (- ?y ?y3) 1)) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
)

;regole di inferenza che rilevano celle contenenti acqua qualora siano vicine ad una cella middle
;caso generale (celle diagonali)...
(defrule remove-g-cell-for-middle 
	(g-cell (x ?x) (y ?y) (content middle))
	?gcell <- (g-cell (x ?gx&:(eq (abs(- ?gx ?x)) 1)) (y ?gy&:(eq (abs(- ?gy ?y)) 1)))
	=>
	(modify ?gcell (probability 0))
)

;...caso quando il middle ha orientamento orizzontale...
(defrule remove-g-cell-for-middle-hor
	(g-cell (x ?x) (y ?y) (content middle))
	(g-cell (x ?x) (y ?y2&:(eq (abs(- ?y ?y2)) 1)) (probability 1))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(and (test (<= (abs(- ?y ?gy)) 1))
		(test (eq (abs(- ?gx ?x)) 1))
	)
	=>
	(modify ?gcell (probability 0))
)

;...e verticale
(defrule remove-g-cell-for-middle-ver
	(g-cell (x ?x) (y ?y) (content middle))
	(g-cell (x ?x2&:(eq (abs(- ?x ?x2)) 1)) (y ?y) (probability 1))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(and (test (<= (abs(- ?x ?gx)) 1))
				(test (eq (abs(- ?gy ?y)) 1))
	)
	=>
	(modify ?gcell (probability 0))
)

;se una cella middle ha dell'acqua sopra o sotto (a destra o a sinistra), allora si può dedurre l'orientamento
;del middle e quindi le celle che sicuramente avranno qualcosa
;caso verticale...
(defrule inference-g-cell-from-middle-ver
	(g-cell (x ?x) (y ?y) (content middle))
	(not (g-cell (y ?yCol&:(eq 1 (abs (- ?y ?yCol)))) (x ?x)))
	?gcellSure <- (g-cell (x ?x2&:(eq 1 (abs (- ?x ?x2)))) (y ?y)  (probability ~1))
	=>
	(modify ?gcellSure (probability 1))
)

;...caso orizzontale
(defrule inference-g-cell-from-middle-hor
	(g-cell (x ?x) (y ?y) (content middle))
	(not (g-cell (x ?xCol&:(eq 1 (abs (- ?x ?xCol)))) (y ?y)))
	?gcellSure <- (g-cell (y ?y2&:(eq 1 (abs (- ?y ?y2)))) (x ?x)  (probability ~1))
	=>
	(modify ?gcellSure (probability 1))
)


;le celle che si trovano in mezzo ad un top/bottom di distanza massimo 3, avranno come contenuto middle
;dato che sicuramente la barca inizierà da top e finirà in bottom
(defrule inference-g-cell-from-near-top-bottom 
	(g-cell (x ?xTop) (y ?y) (content top))
	(g-cell (x ?xBot&:(<= 3 (- ?xBot ?xTop))) (y ?y) (content bot))
	?gcellMiddle <-(g-cell (x ?xMiddle) (y ?y) (content nil))
	(test (and (> ?xMiddle ?xTop) (< ?xMiddle ?xBot)))
	=>
	(modify ?gcellMiddle (content middle))
)

;stessa cosa della regola di sopra ma per left/right
(defrule inference-g-cell-from-near-left-right
	(g-cell (y ?yLeft) (x ?x) (content left))
	(g-cell (y ?yRight&:(<= 3 (- ?yRight ?yLeft))) (x ?x) (content right))
	?gcellMiddle <-(g-cell (y ?yMiddle) (x ?x) (content nil))
	(test (and (> ?yMiddle ?yLeft) (< ?yMiddle ?yRight)))
	=>
	(modify ?gcellMiddle (content middle))
)


;se per una riga il numero di celle candidate è uguale al numero di celle che contengono navi,
;allora tutte le celle avranno sicuramente un pezzo di nave
;riga...
(defrule inference-g-cell-from-row
	(g-per-row (row ?x) (num ?num) (g-cells $?cells))
	(test (eq (length$ $?cells) ?num))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))	
=>
	(modify ?gcell (updated 1) (probability 1))
)

;...colonna
(defrule inference-g-cell-from-col 
	(g-per-col (col ?y) (num ?num) (g-cells $?cells))
	(test (eq (length$ $?cells) ?num))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))	
=>
	(modify ?gcell (updated 1) (probability 1))
)

;per le celle che hanno probabilità 1, non serve effettuare il calcolo della probabilità
(defrule no-update-sure-cell-probability (declare (salience 50))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0) (probability 1))
=>
	(modify ?gcell (updated 1))
)

