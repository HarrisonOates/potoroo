(define (domain travel)
  (:requirements :strips :typing)
  (:types loc)
  (:predicates (at ?l - loc) (road ?a - loc ?b - loc) (rested))
  (:action drive
    :parameters (?from - loc ?to - loc)
    :precondition (and (at ?from) (road ?from ?to))
    :effect (and (not (at ?from)) (at ?to)))
  (:action sleep
    :parameters ()
    :precondition ()
    :effect (rested)))
