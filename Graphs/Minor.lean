import Mathlib

variable {α β : Type*}

def IsMinor (G : SimpleGraph α) (H : SimpleGraph β) : Prop := sorry

infix:50 " ≼ " => IsMinor
