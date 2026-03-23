import Architect
import Graphs.TreeWidth

universe u

variable {α : ℕ → Type u} [∀ n, Fintype (α n)] {G : ∀ n : ℕ, SimpleGraph (α n)} {k : ℕ}

@[blueprint "thm:GMT_bounded_tw"
  (uses := ["thm:kruskal"])]
theorem GMT_bounded_tw (hG : ∀ n, treeWidth (G n) ≤ k) : ∃ i j, i < j ∧ G i ≼ G j := by
  sorry
