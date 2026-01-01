import Graphs.Minor

theorem RobertsonSeymour {α : ℕ → Type _} [∀ n, Fintype (α n)] (G : ∀ n, SimpleGraph (α n)) :
    ∃ i j, i < j ∧ G i ≼ G j := by
  sorry
