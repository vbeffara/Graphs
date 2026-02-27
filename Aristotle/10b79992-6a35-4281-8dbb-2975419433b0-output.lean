/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 10b79992-6a35-4281-8dbb-2975419433b0

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem tree_treeWidth [Fintype α] (hG : G.IsTree) (hG' : G ≠ ⊥) : treeWidth G = 1

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib
import Graphs.Separation
import Graphs.Tree


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

open Classical Set SimpleGraph

universe u

variable {α : Type u} {G : SimpleGraph α}

structure TreeDecomposition (G : SimpleGraph α) where
  ι : Type u
  V : ι → Set α
  T : SimpleGraph ι
  --
  tree : T.IsTree
  union_bags : ⋃ i, V i = univ
  edge_mem_bag {u v : α} : G.Adj u v → ∃ t : ι, u ∈ V t ∧ v ∈ V t
  bag_inter {t₁ t₂ t₃ : ι} : tree.ordered t₁ t₂ t₃ → V t₁ ∩ V t₃ ⊆ V t₂

namespace TreeDecomposition

variable {D : TreeDecomposition G} {t₁ t₂ : D.ι}

def U₁ (D : TreeDecomposition G) (t₁ t₂ : D.ι) : Set α := ⋃ t ∈ D.tree.left t₁ t₂, D.V t

def U₂ (D : TreeDecomposition G) (t₁ t₂ : D.ι) : Set α := ⋃ t ∈ D.tree.right t₁ t₂, D.V t

theorem U_cover (h : D.T.Adj t₁ t₂) : D.U₁ t₁ t₂ ∪ D.U₂ t₁ t₂ = univ := by
  simp [U₁, U₂, ← biUnion_union, D.tree.left_union_right h, D.union_bags]

lemma diestel_12_3_1 (h : D.T.Adj t₁ t₂) : G.Separates (D.U₁ t₁ t₂) (D.U₂ t₁ t₂) (D.V t₁ ∩ D.V t₂) := by
  refine separates_cover (U_cover h) |>.2 ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨w1, ⟨a, rfl⟩, w3, ⟨ha, rfl⟩, hv₁⟩ := hv.1
    obtain ⟨w1, ⟨b, rfl⟩, w3, ⟨hb, rfl⟩, hv₂⟩ := hv.2
    have h1 := D.tree.left_right_ordered h ha hb
    have h2 := D.bag_inter h1.2
    have h3 := D.bag_inter ha
    grind
  · intros u hu v hv huv
    obtain ⟨t₃, ht₃⟩ := D.edge_mem_bag huv
    have h1 := D.tree.left_union_right h
    obtain h2 | h2 := eq_univ_iff_forall.mp h1 t₃
    · obtain ⟨t₄, ht₅, ht₄'⟩ : ∃ t, t ∈ D.tree.right t₁ t₂ ∧ v ∈ D.V t := by
        simpa [U₂] using hv
      have h3 := D.tree.left_right_ordered h h2 ht₅
      have h4 := D.bag_inter h3.1
      have h5 := D.bag_inter h3.2
      grind
    · obtain ⟨t₄, ht₅, ht₄'⟩ : ∃ t, t ∈ D.tree.left t₁ t₂ ∧ u ∈ D.V t := by
        simpa [U₁] using hu
      have h3 := D.tree.left_right_ordered h ht₅ h2
      have h4 := D.bag_inter h2
      have h5 := D.bag_inter h3.1
      grind

theorem adhesion (h : D.T.Adj t₁ t₂) : D.U₁ t₁ t₂ ∩ D.U₂ t₁ t₂ = D.V t₁ ∩ D.V t₂ := by
  ext x; constructor <;> intro hx
  · obtain ⟨y, h1, h2⟩ := diestel_12_3_1 h x hx.1 x hx.2 SimpleGraph.Walk.nil ; simp_all
  · refine ⟨⟨_, ⟨t₁, ?_⟩, hx.1⟩, ⟨_, ⟨t₂, ?_⟩, hx.2⟩⟩ <;>
    simp [SimpleGraph.IsTree.left, SimpleGraph.IsTree.right, SimpleGraph.IsTree.ordered]

def restrict (D : TreeDecomposition G) (H : G.Subgraph) : TreeDecomposition H.coe where
  ι := D.ι
  V t := {v | v.1 ∈ D.V t}
  T := D.T
  tree := D.tree
  union_bags := by simp [iUnion_setOf, ← mem_iUnion, D.union_bags]
  edge_mem_bag {u v} huv := D.edge_mem_bag (H.coe_adj_sub u v huv)
  bag_inter {b₁ b₂ b₃} hordered x hx := D.bag_inter hordered ⟨hx.1, hx.2⟩

noncomputable def width [Fintype α] (D : TreeDecomposition G) : ℕ∞ := ⨆ b, Fintype.card (D.V b) - 1

end TreeDecomposition

noncomputable def treeWidth [Fintype α] (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}

noncomputable section AristotleLemmas

/-
If a graph G is not the empty graph (i.e., it has at least one edge), then its tree-width is at least 1.
-/
theorem treeWidth_ge_one [Fintype α] (h : G ≠ ⊥) : 1 ≤ treeWidth G := by
  -- Since G is not the empty graph, there exists an edge (u, v) in G.
  obtain ⟨u, v, huv⟩ : ∃ u v : α, G.Adj u v := by
    contrapose! h; aesop;
  refine' le_csInf _ _;
  · by_contra h_empty;
    simp_all +decide [ Set.Nonempty ];
    apply h_empty;
    use PUnit, fun _ => Set.univ, ⊥, ?_, ?_, ?_, ?_ <;> norm_num;
    · constructor <;> norm_num [ SimpleGraph.IsTree ];
      simp +decide [ SimpleGraph.connected_iff_exists_forall_reachable ];
    · aesop;
  · rintro w ⟨ D, rfl ⟩;
    obtain ⟨ t, ht ⟩ := D.edge_mem_bag huv;
    refine' le_trans _ ( le_ciSup _ t );
    · refine' Nat.cast_le.mpr ( Nat.le_sub_one_of_lt _ );
      exact Fintype.one_lt_card_iff_nontrivial.mpr ⟨ ⟨ u, ht.1 ⟩, ⟨ v, ht.2 ⟩, by aesop ⟩;
    · simp +zetaDelta at *

/-
In a tree rooted at `root`, for any edge `(u, v)`, either `u` is an ancestor of `v` or `v` is an ancestor of `u`.
-/
lemma SimpleGraph.IsTree.adj_ordered_cases {α : Type*} {G : SimpleGraph α} (hG : G.IsTree) (root : α) {u v : α} (huv : G.Adj u v) :
    hG.ordered root u v ∨ hG.ordered root v u := by
      obtain ⟨ p₁, hp₁ ⟩ := hG.existsUnique_path root u; (obtain ⟨ p₂, hp₂ ⟩ := hG.existsUnique_path root v;);
      -- Since $p₁$ and $p₂$ are paths, they must intersect at some point.
      have h_intersect : p₁.IsPath ∧ p₂.IsPath → u ∈ p₂.support ∨ v ∈ p₁.support := by
        -- By the uniqueness of paths in a tree, if $u$ is not in $p₂$'s support, then there must be a path from $root$ to $u$ that goes through $v$.
        intros h_paths
        by_contra h_contra
        have h_path_root_u_v : ∃ p : G.Walk root u, p.IsPath ∧ v ∈ p.support := by
          use p₂.append (SimpleGraph.Walk.cons huv.symm SimpleGraph.Walk.nil);
          simp_all +decide [ SimpleGraph.Walk.isPath_def ];
          simp_all +decide [ SimpleGraph.Walk.support_append ];
          rw [ List.nodup_append ] ; aesop;
        grind +ring;
      unfold SimpleGraph.IsTree.ordered; aesop;

/-
In a rooted tree, a node has at most one parent.
-/
lemma SimpleGraph.IsTree.parent_unique {α : Type*} {G : SimpleGraph α} (hG : G.IsTree) (root : α) (t : α) (p₁ p₂ : α)
  (h₁ : G.Adj t p₁ ∧ hG.ordered root p₁ t)
  (h₂ : G.Adj t p₂ ∧ hG.ordered root p₂ t) : p₁ = p₂ := by
    -- Since p₁ and p₂ are both adjacent to t and lie on the path from root to t, they must be the same vertex.
    have h_path : ∀ {p : α}, G.Adj t p → hG.ordered root p t → ∀ {q : α}, G.Adj t q → hG.ordered root q t → p = q := by
      intros p hp hpath_p q hq hpath_q
      have h_path_eq : (hG.path root t).1 = (hG.path root p).1.append (hG.path p t).1 ∧ (hG.path root t).1 = (hG.path root q).1.append (hG.path q t).1 := by
        exact ⟨ hG.path_split hpath_p, hG.path_split hpath_q ⟩;
      have h_support_eq : (hG.path p t).1.support = [p, t] ∧ (hG.path q t).1.support = [q, t] := by
        have h_support_eq : ∀ {p : α}, G.Adj t p → (hG.path p t).1.support = [p, t] := by
          intro p hp; have := hG.path_adj hp.symm; aesop;
        exact ⟨ h_support_eq hp, h_support_eq hq ⟩;
      have h_support_eq : (hG.path root t).1.support = (hG.path root p).1.support ++ [t] ∧ (hG.path root t).1.support = (hG.path root q).1.support ++ [t] := by
        have := congr_arg SimpleGraph.Walk.support h_path_eq.1; have := congr_arg SimpleGraph.Walk.support h_path_eq.2; simp_all +decide [ SimpleGraph.Walk.support_append ] ;
      have h_support_eq : (hG.path root p).1.support.getLast? = some p ∧ (hG.path root q).1.support.getLast? = some q := by
        have h_support_eq : ∀ {u v : α} (p : G.Walk u v), p.support.getLast? = some v := by
          intro u v p; induction p <;> simp +decide [ * ] ;
          grind;
        exact ⟨ h_support_eq _, h_support_eq _ ⟩;
      aesop;
    exact h_path h₁.1 h₁.2 h₂.1 h₂.2

/-
Transitivity of the ancestor relation in a rooted tree.
-/
lemma SimpleGraph.IsTree.ordered_trans {α : Type*} {G : SimpleGraph α} (hG : G.IsTree) (root : α) {a b c : α}
    (hab : hG.ordered root a b) (hbc : hG.ordered root b c) : hG.ordered root a c := by
      -- By definition of `IsTree`, since there is a path from `root` to `b` and from `root` to `c`, and `b` is on the path from `root` to `c`, the path from `root` to `c` is the concatenation of the path from `root` to `b` and the path from `b` to `c`.
      have h_concat : (hG.path root c).1 = (hG.path root b).1.append (hG.path b c).1 := by
        exact?;
      unfold SimpleGraph.IsTree.ordered at *; aesop;

/-
Antisymmetry of the ancestor relation in a rooted tree.
-/
lemma SimpleGraph.IsTree.ordered_antisymm {α : Type*} {G : SimpleGraph α} (hG : G.IsTree) (root : α) {a b : α}
    (hab : hG.ordered root a b) (hba : hG.ordered root b a) : a = b := by
      -- By the uniqueness of paths in a tree, the path from `root` to `b` and the path from `root` to `a` must be the same.
      have h_path_eq : (hG.path root b).1 = (hG.path root a).1.append (hG.path a b).1 := by
        exact?;
      have h_path_eq' : (hG.path root a).1 = (hG.path root b).1.append (hG.path b a).1 := by
        exact?;
      replace h_path_eq' := congr_arg ( fun p => p.support ) h_path_eq'; simp_all +decide [ SimpleGraph.Walk.support_append ] ;
      cases h : ( hG.path a b : G.Walk a b ) <;> aesop

/-
The intersection property for the specific tree decomposition bags: if a node is in the bags of two nodes, it is in the bag of any node on the path between them.
-/
def tree_bag [Fintype α] (hG : G.IsTree) (root : α) (t : α) : Set α :=
  insert t {p | G.Adj t p ∧ hG.ordered root p t}

lemma tree_bag_inter [Fintype α] (hG : G.IsTree) (root : α) {t₁ t₂ t₃ : α}
    (h_ordered : hG.ordered t₁ t₂ t₃) :
    tree_bag hG root t₁ ∩ tree_bag hG root t₃ ⊆ tree_bag hG root t₂ := by
      intro x hx
      obtain ⟨hx₁, hx₃⟩ := hx;
      -- Since x is in the tree bag of t₁ and t₃, it is adjacent to t₁ and t₃ or equal to them.
      have h_adj : G.Adj x t₁ ∨ x = t₁ := by
        cases hx₁ ; aesop;
        exact Or.inl ( by rename_i h; exact h.1.symm )
      have h_adj' : G.Adj x t₃ ∨ x = t₃ := by
        cases hx₃ <;> simp_all +decide [ SimpleGraph.IsTree.ordered ];
        exact Or.inl ( by tauto );
      have h_path : ∃ p : G.Walk t₁ t₃, p.support ⊆ [t₁, x, t₃] := by
        rcases h_adj with ( h_adj | rfl ) <;> rcases h_adj' with ( h_adj' | rfl );
        · exact ⟨ SimpleGraph.Walk.cons h_adj.symm ( SimpleGraph.Walk.cons h_adj' SimpleGraph.Walk.nil ), by simp +decide ⟩;
        · exact ⟨ SimpleGraph.Walk.cons h_adj.symm SimpleGraph.Walk.nil, by simp +decide ⟩;
        · exact ⟨ SimpleGraph.Walk.cons h_adj' SimpleGraph.Walk.nil, by simp +decide ⟩;
        · exact ⟨ SimpleGraph.Walk.nil, by simp +decide ⟩;
      obtain ⟨ p, hp ⟩ := h_path;
      have h_path : t₂ ∈ p.support := by
        have h_unique_path : ∀ (p q : G.Walk t₁ t₃), p.IsPath → q.IsPath → p = q := by
          have := hG.existsUnique_path t₁ t₃;
          exact fun p q hp hq => this.unique hp hq;
        contrapose! h_unique_path;
        refine' ⟨ p.toPath, hG.path t₁ t₃, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.isPath_def ];
        intro h; have := hG.ordered t₁ t₂ t₃; simp_all +decide [ SimpleGraph.IsTree.ordered ] ;
        replace h := congr_arg ( fun q => t₂ ∈ q.support ) h ; simp_all +decide [ SimpleGraph.Walk.toPath ] ;
        exact h_unique_path ( by simpa using SimpleGraph.Walk.support_bypass_subset p h );
      have h_path : t₂ ∈ [t₁, x, t₃] := by
        exact hp h_path;
      unfold tree_bag at *; aesop;

/-
Constructs a tree decomposition of a tree `G` where the decomposition tree is `G` itself and bags are `{node, parent}`.
-/
noncomputable def treeDecompositionOfTree [Fintype α] (hG : G.IsTree) (root : α) : TreeDecomposition G where
  ι := α
  V := tree_bag hG root
  T := G
  tree := hG
  union_bags := by
    exact Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨ x, Set.mem_insert _ _ ⟩
  edge_mem_bag := by
    -- Let `uv` be an edge. By `adj_ordered_cases`, either `ordered root u v` or `ordered root v u`.
    intro u v huv
    by_cases h_ordered : hG.ordered root u v;
    · -- Since $u$ is the parent of $v$, we have $u \in \text{tree\_bag } hG \text{ root } v$ and $v \in \text{tree\_bag } hG \text{ root } v$.
      use v
      simp [tree_bag, h_ordered];
      exact Or.inr huv.symm;
    · -- Since `¬hG.ordered root u v`, we have `hG.ordered root v u`.
      have h_ordered_rev : hG.ordered root v u := by
        exact Or.resolve_left ( hG.adj_ordered_cases root huv ) h_ordered;
      unfold tree_bag; aesop;
  bag_inter := by
    exact?

/-
Constructs a tree decomposition of a tree `G` where the decomposition tree is `G` itself and bags are `{node, parent}`.
-/
noncomputable def treeDecompositionOfTree' [Fintype α] (hG : G.IsTree) (root : α) : TreeDecomposition G where
  ι := α
  V := tree_bag hG root
  T := G
  tree := hG
  union_bags := by
    exact Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨ x, Set.mem_insert _ _ ⟩
  edge_mem_bag := by
    intro u v huv
    have h_cases : hG.ordered root u v ∨ hG.ordered root v u := by
      exact?;
    cases' h_cases with h h;
    · use v;
      unfold tree_bag;
      simp_all +decide [ SimpleGraph.adj_comm ];
    · unfold tree_bag; aesop;
  bag_inter := by
    exact?

/-
The width of the canonical tree decomposition of a tree is at most 1.
-/
lemma treeDecompositionOfTree'_width [Fintype α] (hG : G.IsTree) (root : α) :
    (treeDecompositionOfTree' hG root).width ≤ 1 := by
      -- Each bag in the tree decomposition contains at most 2 vertices, so the width is at most 1.
      have h_card : ∀ t : α, (Fintype.card (tree_bag hG root t)) ≤ 2 := by
        intros t
        set parents := {p | G.Adj t p ∧ hG.ordered root p t}
        have h_parents_card : parents.ncard ≤ 1 := by
          have h_parents_card : ∀ p₁ p₂ : α, p₁ ∈ parents → p₂ ∈ parents → p₁ = p₂ := by
            intro p₁ p₂ hp₁ hp₂; have := SimpleGraph.IsTree.parent_unique hG root t p₁ p₂; aesop;
          exact?;
        have h_card : (tree_bag hG root t).ncard ≤ 1 + parents.ncard := by
          convert Set.ncard_union_le { t } parents using 1 ; aesop;
        simpa [ Set.ncard_eq_toFinset_card' ] using h_card.trans ( add_le_add_left h_parents_card _ );
      convert ciSup_le fun t => Nat.cast_le.mpr ( Nat.sub_le_sub_right ( h_card t ) 1 ) using 1;
      · exact ⟨ root ⟩;
      · infer_instance;
      · exact fun _ => inferInstance;
      · infer_instance

end AristotleLemmas

theorem tree_treeWidth [Fintype α] (hG : G.IsTree) (hG' : G ≠ ⊥) : treeWidth G = 1 :=
  by
    refine' le_antisymm _ _;
    · refine' le_trans ( csInf_le _ _ ) _;
      exact ( treeDecompositionOfTree' hG ( Classical.choose ( show ∃ x : α, True from by
                                                                contrapose! hG'; aesop ) ) ).width
      all_goals generalize_proofs at *;
      · exact ⟨ 0, fun w hw => hw.choose_spec.symm ▸ zero_le _ ⟩;
      · exact ⟨ _, rfl ⟩;
      · exact?;
    · exact?