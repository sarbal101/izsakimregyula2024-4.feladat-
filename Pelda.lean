set_option linter.unusedVariables false

theorem TetelNeve {a b :R}(Kontextus:a = b):b = a:= by
  --Bizonyitas levezetese taktikakkal
  exact Eq.symm Kontextus

theorem pelda {p q :Prop}: p → q → p := fun hp : p => fun hq : q => hp
