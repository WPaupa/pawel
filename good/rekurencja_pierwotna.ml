-- Aplikacja intów w Pawle bardzo naturalnie wynika
-- z rekurencji pierwotnej.


-- Jednakże nie tylko funkcje pierwotnie rekurencyjne
-- są wyrażalne w Pawle za pomocą aplikacji.

let ackermann m = m (λA. (λn. ({+} n 1) A 1)) (id + 1);;