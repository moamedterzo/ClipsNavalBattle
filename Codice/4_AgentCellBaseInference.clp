(defmodule AGENT_CELL_BASE_INFERENCE (import AGENT ?ALL))


;regola che scala di uno i candidati quando la probabilità è 0
(defrule manage-water-g-cell (declare (salience 10))
	?gcell <- (g-cell (x ?x) (y ?y) (probability 0))
	?row <- (g-per-row (row ?x) (g-cells $?rows) (gk-cells $?gkrows))
	?col <- (g-per-col (col ?y) (g-cells $?cols) (gk-cells $?gkcols))
=>
	(printout t "REMOVED cell [" ?x ", " ?y "]" crlf)
	(retract ?gcell)	
	(assert (k-cell (x ?x) (y ?y) (content water)))
	(modify ?row (g-cells (delete-member$ $?rows ?y)) (gk-cells (delete-member$ $?gkrows ?y)))
	(modify ?col (g-cells (delete-member$ $?cols ?x)) (gk-cells (delete-member$ $?gkcols ?x)))
)

;ogni volta che c'è una nuova k-cell, aggiorno la probabilità della g-cell
(defrule initialize-fired-g-cell-boat (declare (salience 10))
	(k-cell (x ?x) (y ?y) (content ?content&~water))
	?gcell <- (g-cell (x ?x) (y ?y) (content nil))
=>
	(modify ?gcell (probability 1) (content ?content))
)


;ogni volta che c'è una g-cell sicura, aggiorno il conteggio delle righe e colonne
(defrule update-candidate-g-cell-boat 
	(g-cell (x ?x) (y ?y) (probability 1))
	?row <- (g-per-row (row ?x) (num ?numRow) (g-cells $?rows))
	?col <- (g-per-col (col ?y) (num ?numCol) (g-cells $?cols))
	(test(and (member$ ?y $?rows) (member$ ?x $?cols)))
=>	
	(modify ?row (num (- ?numRow 1)) (g-cells (delete-member$ $?rows ?y)))
	(modify ?col (num (- ?numCol 1)) (g-cells (delete-member$ $?cols ?x)))
)


;quando trovo una cella sicura, devo capire la forma delle navi
(defrule update-boats-from-g-cell-sub
	(g-cell (x ?x) (y ?y) (content sub))
=>	
	(assert (g-boat (size 1) (mainColRow ?x) (secColRow ?y) (alignment hor)));le navi sub hanno orientamento orizzontale
)

(defrule update-boats-from-g-cell-top-bot-2
	(g-cell (x ?x) (y ?y) (content top))
	(g-cell (x ?x2&:(eq ?x (- ?x2 1))) (y ?y) (content bot))
=>	
	(assert (g-boat (size 2) (mainColRow ?y) (secColRow ?x ?x2) (alignment ver)))
)

(defrule update-boats-from-g-cell-top-bot-3
	(g-cell (x ?x) (y ?y) (content top))
	(g-cell (x ?x2&:(eq ?x (- ?x2 2))) (y ?y) (content bot))
=>	
	(bind ?x3 (+ ?x 1))
	(assert (g-boat (size 3) (mainColRow ?y) (secColRow ?x ?x3 ?x2) (alignment ver)))
)

(defrule update-boats-from-g-cell-top-bot-4
	(g-cell (x ?x) (y ?y) (content top))
	(g-cell (x ?x2&:(eq ?x (- ?x2 3))) (y ?y) (content bot))
=>	
	(bind ?x3 (+ ?x 1))
	(bind ?x4 (+ ?x 2))
	(assert (g-boat (size 4) (mainColRow ?y) (secColRow ?x ?x3 ?x4 ?x2) (alignment ver)))
)

(defrule update-boats-from-g-cell-left-right-2
	(g-cell (y ?y) (x ?x) (content left))
	(g-cell (y ?y2&:(eq ?y (- ?y2 1))) (x ?x) (content right))
=>	
	(assert (g-boat (size 2) (mainColRow ?x) (secColRow ?y ?y2) (alignment hor)))
)

(defrule update-boats-from-g-cell-left-right-3
	(g-cell (y ?y) (x ?x) (content left))
	(g-cell (y ?y2&:(eq ?y (- ?y2 2))) (x ?x) (content right))
=>	
	(bind ?y3 (+ ?y 1))
	(assert (g-boat (size 3) (mainColRow ?x) (secColRow ?y ?y3 ?y2) (alignment hor)))
)

(defrule update-boats-from-g-cell-left-right-4
	(g-cell (y ?y) (x ?x) (content left))
	(g-cell (y ?y2&:(eq ?y (- ?y2 3))) (x ?x) (content right))
=>	
	(bind ?y3 (+ ?y 1))
	(bind ?y4 (+ ?y 2))
	(assert (g-boat (size 4) (mainColRow ?x) (secColRow ?y ?y3 ?y4 ?y2) (alignment hor)))
)

;se trovo 4 celle attaccate, corrispondono ad una nave da 4 per forza
(defrule find-4-boat-hor
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
(defrule find-4-boat-ver
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

;regole che indicano quando sono finite le navi da 4, 3 o 2
(defrule found-all-boat-1
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

(defrule found-all-boat-2
	?boat2a <- (g-boat (size 2))
	?boat2b <- (g-boat (size 2))
	?boat2c <- (g-boat (size 2))
	(test (and (< (fact-index ?boat2a) (fact-index ?boat2b)) 
			   (< (fact-index ?boat2b) (fact-index ?boat2c))))
	=>
	(assert (found-all-boats 2))
)

(defrule found-all-boat-3
	?boat3a <- (g-boat (size 3))
	?boat3b <- (g-boat (size 3))
	(test (< (fact-index ?boat3a) (fact-index ?boat3b)))
	=>
	(assert (found-all-boats 3))
)

(defrule found-all-boat-4
	(g-boat (size 4))
=>
	(assert (found-all-boats 4))
)

;se trovo 3 celle tutte insieme e ho trovato la nave da 4, allora è una nave da 3
(defrule find-3-boat-hor
	?gcellLeft <- (g-cell (y ?y1) (x ?x) (probability 1) (content ?c1))
	?gcellMiddle1 <- (g-cell (y ?y2&:(eq ?y1 (- ?y2 1))) (x ?x) (probability 1) (content ?c2))
	?gcellRight <- (g-cell (y ?y3&:(eq ?y1 (- ?y3 2))) (x ?x) (probability 1) (content ?c3))
	(found-all-boats 4)
	(test (or (eq ?c1 nil) 
			  (eq ?c2 nil)
			  (eq ?c3 nil)))
=>	
	(modify ?gcellLeft (content left))
	(modify ?gcellMiddle1 (content middle))
	(modify ?gcellRight (content right))
	(assert (g-boat (size 3) (mainColRow ?x) (secColRow ?y1 ?y2 ?y3) (alignment hor)))
)
(defrule find-3-boat-ver
	?gcellTop <- (g-cell (x ?x1) (y ?y) (probability 1) (content ?c1))
	?gcellMiddle1 <- (g-cell (x ?x2&:(eq ?x1 (- ?x2 1))) (y ?y) (probability 1) (content ?c2))
	?gcellBot <- (g-cell (x ?x3&:(eq ?x1 (- ?x3 2))) (y ?y) (probability 1) (content ?c3))
	(found-all-boats 4)
	(test (or (eq ?c1 nil) 
			  (eq ?c2 nil)
			  (eq ?c3 nil)))
=>	
	(modify ?gcellTop (content top))
	(modify ?gcellMiddle1 (content middle))
	(modify ?gcellBot (content bot))
	(assert (g-boat (size 3) (mainColRow ?y) (secColRow ?x1 ?x2 ?x3) (alignment ver)))
)

;si trovano le navi da 2 quando le navi da 3 o 4 sono state tutte trovate
(defrule find-2-boat-hor
	?gcellLeft <- (g-cell (y ?y1) (x ?x) (probability 1) (content ?c1))
	?gcellRight <- (g-cell (y ?y2&:(eq ?y1 (- ?y2 1))) (x ?x) (probability 1) (content ?c2))
	(found-all-boats 4)
	(found-all-boats 3)
	(test (or (eq ?c1 nil) 
			  (eq ?c2 nil)))
=>	
	(modify ?gcellLeft (content left))
	(modify ?gcellRight (content right))
	(assert (g-boat (size 2) (mainColRow ?x) (secColRow ?y1 ?y2) (alignment hor)))
)
(defrule find-2-boat-ver
	?gcellTop <- (g-cell (x ?x1) (y ?y) (probability 1) (content ?c1))
	?gcellBot <- (g-cell (x ?x2&:(eq ?x1 (- ?x2 1))) (y ?y) (probability 1) (content ?c2))
	(found-all-boats 4)
	(found-all-boats 3)
	(test (or (eq ?c1 nil) 
			  (eq ?c2 nil)))
=>	
	(modify ?gcellTop (content top))
	(modify ?gcellBot (content bot))
	(assert (g-boat (size 2) (mainColRow ?y) (secColRow ?x1 ?x2) (alignment ver)))
)

;se sono rimaste solo navi sub, allora tutte le celle sicure sono sub
(defrule find-1-boat-sub
	?gcellSub <- (g-cell (y ?y) (x ?x) (probability 1) (content nil))
	(found-all-boats 4)
	(found-all-boats 3)
	(found-all-boats 2)
=>	
	(modify ?gcellSub (content sub))
	(assert (g-boat (size 1) (mainColRow ?x) (secColRow ?y) (alignment hor)))
)

;se ci sono 2 celle contigue ma le navi da 2 sono state tutte pescate, allora è almeno una nave da 3
(defrule extend-2-boat-from-hor
	(found-all-boats 2)
	(g-cell (y ?y1) (x ?x) (probability 1) (content left|right))
	?gcellMiddle1 <- (g-cell (y ?y2&:(eq 1 (abs (- ?y1 ?y2)))) (x ?x) (probability 1) (content nil))
	?gcellExt <- (g-cell (y ?y3&:(eq 1 (abs (- ?y1 ?y3)))) (x ?x))	
=>	
	(modify ?gcellMiddle1 (content middle))
	(modify ?gcellExt (probability 1))
)

(defrule extend-2-boat-from-ver
	(found-all-boats 2)
	(g-cell (x ?x1) (y ?y) (probability 1) (content bot|top))
	?gcellMiddle1 <- (g-cell (x ?x2&:(eq 1 (abs (- ?x1 ?x2)))) (y ?y) (probability 1) (content nil))
	?gcellExt <- (g-cell (x ?x3&:(eq 1 (abs (- ?x1 ?x3)))) (y ?y))	
=>	
	(modify ?gcellMiddle1 (content middle))
	(modify ?gcellExt (probability 1))
)

;se ci sono 3 celle contigue ma le navi da 3 sono state tutte pescate, allora è una nave da 4
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


;inferenze basate sulle navi rimanenti


;tengo aggiornato il numero di celle per le quali non si conosce ancora il contenuto
(defrule update-known-boat-for-col
	(g-boat (alignment hor) (mainColRow ?x) (secColRow $? ?y $?))
	?row <- (g-per-row (row ?x) (gk-cells $?rows))
	?col <- (g-per-col (col ?y) (gk-cells $?cols))
	(test(and (member$ ?y $?rows) (member$ ?x $?cols)))
=>	
	(modify ?row (gk-cells (delete-member$ $?rows ?y)))
	(modify ?col (gk-cells (delete-member$ $?cols ?x)))
)
(defrule update-known-boat-for-row
	(g-boat (alignment ver) (mainColRow ?y) (secColRow $? ?x $?))
	?row <- (g-per-row (row ?x) (gk-cells $?rows))
	?col <- (g-per-col (col ?y) (gk-cells $?cols))
	(test(and (member$ ?y $?rows) (member$ ?x $?cols)))
=>	
	(modify ?row (gk-cells (delete-member$ $?rows ?y)))
	(modify ?col (gk-cells (delete-member$ $?cols ?x)))
)


(defrule only-one-slot-for-4-boat
	(g-per-row (row ?x) (gk-cells $?rowCells&:(>= (length$ $?rowCells) 4)))

	=> (assert (only-one-slot-for-4-boat))
)


;rimozione celle troppo piccole per contenere una nave
(defrule remove-g-cell-no-2-boat 
	(found-all-boats 1)
	?gcell <-(g-cell (x ?x) (y ?y) (content nil))

	?xm1 <- (- ?x 1)
	?xp1 <- (+ ?x 1)
	?ym1 <- (- ?y 1)
	?yp1 <- (+ ?y 1)

	(and (not (g-per-row (row ?x) (gk-cells $? ?ym1 ?y $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?y ?yp1 $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm1 ?x $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?x ?xp1 $?)))
	)
	=>
	(modify ?gcell (probability 0))
)
(defrule remove-g-cell-no-3-boat 
	(found-all-boats 1)
	(found-all-boats 2)
	?gcell <-(g-cell (x ?x) (y ?y) (content nil))
	
	?xm1 <- (- ?x 1)
	?xm2 <- (- ?x 2)
	?xp1 <- (+ ?x 1)
	?xp2 <- (+ ?x 2)
	?ym1 <- (- ?y 1)
	?ym2 <- (- ?y 2)
	?yp1 <- (+ ?y 1)
	?yp2 <- (+ ?y 2)

	(and (not (g-per-row (row ?x) (gk-cells $? ?ym2 ?ym1 ?y $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?ym1 ?y ?yp1 $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?y ?yp1 ?yp2 $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm2 ?xm1 ?x $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm1 ?x ?xp1 $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?x ?xp1 ?xp2 $?)))
	)
	=>
	(modify ?gcell (probability 0))
)
(defrule remove-g-cell-no-4-boat 
	(found-all-boats 1)
	(found-all-boats 2)
	(found-all-boats 3)
	?gcell <-(g-cell (x ?x) (y ?y) (content nil))
	
	?xm1 <- (- ?x 1)
	?xm2 <- (- ?x 2)
	?xm3 <- (- ?x 3)
	?xp1 <- (+ ?x 1)
	?xp2 <- (+ ?x 2)
	?xp3 <- (+ ?x 3)
	?ym1 <- (- ?y 1)
	?ym2 <- (- ?y 2)
	?ym3 <- (- ?y 3)
	?yp1 <- (+ ?y 1)
	?yp2 <- (+ ?y 2)
	?yp3 <- (+ ?y 3)

	(and (not (g-per-row (row ?x) (gk-cells $? ?ym3 ?ym2 ?ym1 ?y $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?ym2 ?ym1 ?y ?yp1 $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?ym1 ?y ?yp1 ?yp2 $?)))
		 (not (g-per-row (row ?x) (gk-cells $? ?y ?yp1 ?yp2 ?yp3 $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm3 ?xm2 ?xm1 ?x $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm2 ?xm1 ?x ?xp1 $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?xm1 ?x ?xp1 ?xp2 $?)))
		 (not (g-per-col (col ?y) (gk-cells $? ?x ?xp1 ?xp2 ?xp3 $?)))
	)
	=>
	(modify ?gcell (probability 0))
)

;regola che vede se esiste un unico slot possibile per una nave da 4
(defrule reveal-for-4-boat 
	(not (found-all-boats 4))
	(only-one-slot-for-4-boat)
	
	=>
)



;fine inferenze basate su navi rimanenti






;;;;;

;le celle che hanno acqua hanno probabilità 0 di avere una nave
(defrule remove-k-cell-water 
	?gcell <- (g-cell (x ?x) (y ?y))
	(k-cell (x ?x) (y ?y) (content water))
=>
	(modify ?gcell (probability 0))
)

;celle che hanno righe o colonne vuote (bisogna escludere quelle celle per le quali la probabilità è certa)
(defrule remove-g-cell-col 
	(g-per-col (col ?y) (num 0))
	?gcell <- (g-cell (y ?y) (x ?x) (probability ~1))
	=>
	(modify ?gcell (probability 0))
)

(defrule remove-g-cell-row 
	(g-per-row (row ?x) (num 0))
	?gcell <- (g-cell (x ?x) (y ?y) (probability ~1))
	=>
	(modify ?gcell (probability 0))
)

;rimozione g-cell per sottomarino
(defrule remove-g-cell-sub 
	(g-cell (x ?x) (y ?y) (content sub))
	?gcell <- (g-cell (x ?gx&:(<= (abs(- ?gx ?x)) 1)) (y ?gy&:(<= (abs(- ?gy ?y)) 1)))
	=>
	(modify ?gcell (probability 0))
)
;inferenza sulla presenza di un sottomarino
(defrule inference-g-cell-sub 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(and (not (g-cell (x ?x) (y ?y2&:(eq 1 (abs (- ?y ?y2))))))
	 	 (not (g-cell (x ?x2&:(eq 1 (abs (- ?x ?x2)))) (y ?y2)))
	)
	=>
	(modify ?gcell (content sub))
)

;inferenza su top, botton, left, right
;se ho qualcosa sotto ma non ho niente sopra, allora è top
(defrule inference-g-cell-content-top 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (x ?x2&:(eq ?x2 (+ ?x 1))) (y ?y) (probability 1))
	(not (g-cell (x ?x3&:(eq ?x3 (- ?x 1))) (y ?y)))
	=>
	(modify ?gcell (content top))
)
(defrule inference-g-cell-content-bottom 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (x ?x2&:(eq ?x2 (- ?x 1))) (y ?y) (probability 1))
	(not (g-cell (x ?x3&:(eq ?x3 (+ ?x 1))) (y ?y)))
	=>
	(modify ?gcell (content bot))
)
(defrule inference-g-cell-content-left 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (y ?y2&:(eq ?y2 (+ ?y 1))) (x ?x) (probability 1))
	(not (g-cell (y ?y3&:(eq ?y3 (- ?y 1))) (x ?x)))
	=>
	(modify ?gcell (content left))
)
(defrule inference-g-cell-content-right 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (y ?y2&:(eq ?y2 (- ?y 1))) (x ?x) (probability 1))
	(not (g-cell (y ?y3&:(eq ?y3 (+ ?y 1))) (x ?x)))
	=>
	(modify ?gcell (content right))
)

;rilevamento dei middle
(defrule inference-g-cell-middle-horizontal 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (y ?y2&:(eq ?y2 (- ?y 1))) (x ?x) (probability 1))
	(g-cell (y ?y3&:(eq ?y3 (+ ?y 1))) (x ?x) (probability 1))
	=>
	(modify ?gcell (content middle))
)
(defrule inference-g-cell-middle-vertical 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (x ?x2&:(eq ?x2 (- ?x 1))) (y ?y) (probability 1))
	(g-cell (x ?x3&:(eq ?x3 (+ ?x 1))) (y ?y) (probability 1))
	=>
	(modify ?gcell (content middle))
)

;rimozione e inferenza celle in base al contenuto
(defrule remove-g-cell-top 
	(g-cell (x ?x) (y ?y) (content top))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?x ?gx) 1))
		     (test (eq ?gy ?y))
                )

		(and (test (<= (abs (- ?gx ?x)) 1))
		     (test (eq (abs (- ?gy ?y)) 1))
                )

		(and (test (eq (- ?gx ?x) 2))
		     (test (eq (abs (- ?gy ?y)) 1))
                )
	)
	=>
	(modify ?gcell (probability 0))
)

(defrule inference-g-cell-top 
	(g-cell (x ?x) (y ?y) (content top))
	?gcellSure <- (g-cell (x ?x2&:(eq (- ?x2 1) ?x)) (y ?y) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x2 ", " ?y "]" crlf)
)


(defrule remove-g-cell-bottom 
	(g-cell (x ?x) (y ?y) (content bot))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?gx ?x) 1))
		     (test (eq ?gy ?y))
                )

		(and (test (<= (abs (- ?gx ?x)) 1))
		     (test (eq (abs (- ?gy ?y)) 1))
                )

		(and (test (eq (- ?x ?gx) 2))
		     (test (eq (abs (- ?gy ?y)) 1))
                )
	)
	=>
	(modify ?gcell (probability 0))
)

(defrule inference-g-cell-bottom
	(g-cell (x ?x) (y ?y) (content bot))
	?gcellSure <- (g-cell (x ?x2&:(eq (- ?x 1) ?x2)) (y ?y) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x2 ", " ?y "]" crlf)
)


(defrule remove-g-cell-left 
	(g-cell (x ?x) (y ?y) (content left))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?y ?gy) 1))
		     (test (eq ?gx ?x))
                )

		(and (test (<= (abs (- ?gy ?y)) 1))
		     (test (eq (abs (- ?gx ?x)) 1))
                )

		(and (test (eq (- ?gy ?y) 2))
		     (test (eq (abs (- ?gx ?x)) 1))
                )
	)
	=>
	(modify ?gcell (probability 0))
)

(defrule inference-g-cell-left 
	(g-cell (x ?x) (y ?y) (content left))
	?gcellSure <- (g-cell (x ?x) (y ?y2&:(eq (- ?y2 1) ?y)) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x ", " ?y2 "]" crlf)
)

(defrule remove-g-cell-right
	(g-cell (x ?x) (y ?y) (content right))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?gy ?y) 1))
		     (test (eq ?gx ?x))
                )

		(and (test (<= (abs (- ?y ?gy)) 1))
		     (test (eq (abs (- ?gx ?x)) 1))
                )

		(and (test (eq (- ?y ?gy) 2))
		     (test (eq (abs (- ?gx ?x)) 1))
                )
	)
	=>
	(modify ?gcell (probability 0))
)

(defrule inference-g-cell-right 
	(g-cell (x ?x) (y ?y) (content right))
	?gcellSure <- (g-cell (x ?x) (y ?y2&:(eq (- ?y 1) ?y2)) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x ", " ?y2 "]" crlf)
)



;regole di inferenza per la cella middle
(defrule g-cell-continue-middle-from-top 
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x2&:(eq (- ?x ?x2) 1)) (y ?y) (probability 1))
 ?gcellSure <- (g-cell (x ?x3&:(eq (- ?x3 ?x) 1)) (y ?y) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-bottom
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x2&:(eq (- ?x2 ?x) 1)) (y ?y) (probability 1))
 ?gcellSure <- (g-cell (x ?x3&:(eq (- ?x ?x3) 1)) (y ?y) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-left 
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x) (y ?y2&:(eq (- ?y ?y2) 1)) (probability 1))
 ?gcellSure <- (g-cell (x ?x) (y ?y3&:(eq (- ?y3 ?y) 1)) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-right 
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x) (y ?y2&:(eq (- ?y2 ?y) 1)) (probability 1))
 ?gcellSure <- (g-cell (x ?x) (y ?y3&:(eq (- ?y ?y3) 1)) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

;regola di inferenza che rimuove le celle per middle
(defrule remove-g-cell-middle 
 (g-cell (x ?x) (y ?y) (content middle))
 ?gcell <- (g-cell (x ?gx&:(eq (abs(- ?gx ?x)) 1)) (y ?gy&:(eq (abs(- ?gy ?y)) 1)))
 =>
   (modify ?gcell (probability 0))
)
;gestione middle quando si inferisce che è verticale
(defrule infer-from-middle-vertical 
(g-cell (x ?x) (y ?y) (content middle))
(not (g-cell (y ?yCol&:(eq 1 (abs (- ?y ?yCol)))) (x ?x)))
 ?gcellSure <- (g-cell (x ?x2&:(eq 1 (abs (- ?x ?x2)))) (y ?y)  (probability ~1))
=>
 (modify ?gcellSure (probability 1))
)

(defrule infer-from-middle-horizontal
(g-cell (x ?x) (y ?y) (content middle))
(not (g-cell (x ?xCol&:(eq 1 (abs (- ?x ?xCol)))) (y ?y)))
 ?gcellSure <- (g-cell (y ?y2&:(eq 1 (abs (- ?y ?y2)))) (x ?x)  (probability ~1))
=>
 (modify ?gcellSure (probability 1))
)

;rimozione delle celle escluse dal middle orizzontale
(defrule remove-g-cell-middle-horizontal
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x) (y ?y2&:(eq (abs(- ?y ?y2)) 1)) (probability 1))
 ?gcell <- (g-cell (x ?gx) (y ?gy))
 (and (test (<= (abs(- ?y ?gy)) 1))
	  (test (eq (abs(- ?gx ?x)) 1))
 )
 =>
	(modify ?gcell (probability 0))
)

;rimozione delle celle escluse dal middle verticale
(defrule remove-g-cell-middle-vertical
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x2&:(eq (abs(- ?x ?x2)) 1)) (y ?y) (probability 1))
 ?gcell <- (g-cell (x ?gx) (y ?gy))
 (and (test (<= (abs(- ?x ?gx)) 1))
			 (test (eq (abs(- ?gy ?y)) 1))
 )
 =>
(modify ?gcell (probability 0))
)

;si trovano le celle che si trovano in mezzo ad un top/bottom
(defrule find-g-cell-from-top-bottom 
 (g-cell (x ?xTop) (y ?y) (content top))
 (g-cell (x ?xBot&:(<= 3 (- ?xBot ?xTop))) (y ?y) (content bot))
 ?gcellMiddle <-(g-cell (x ?xMiddle) (y ?y) (content nil))
 (test (and (> ?xMiddle ?xTop) (< ?xMiddle ?xBot)))
 =>
(modify ?gcellMiddle (content middle))
)

;si trovano le celle che si trovano in mezzo ad un left/right
(defrule find-g-cell-from-left-right 
 (g-cell (y ?yLeft) (x ?x) (content left))
 (g-cell (y ?yRight&:(<= 3 (- ?yRight ?yLeft))) (x ?x) (content right))
  ?gcellMiddle <-(g-cell (y ?yMiddle) (x ?x) (content nil))
 (test (and (> ?yMiddle ?yLeft) (< ?yMiddle ?yRight)))
 =>
(modify ?gcellMiddle (content middle))
)


;inferenze per quelle righe o colonne che hanno tutti gli elementi contenenti navi
(defrule update-g-cell-probability-row
	(g-per-row (row ?x) (num ?num) (g-cells $?rows))
	(test (eq (length$ $?rows) ?num))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))	
=>
	(modify ?gcell (updated 1) (probability 1))
)

(defrule update-g-cell-probability-col 
	(g-per-col (col ?y) (num ?num) (g-cells $?cols))
	(test (eq (length$ $?cols) ?num))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))	
=>
	(modify ?gcell (updated 1) (probability 1))
)



(defrule no-update-sure-cell-probability 
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0) (probability 1))
=>
	(modify ?gcell (updated 1))
)

