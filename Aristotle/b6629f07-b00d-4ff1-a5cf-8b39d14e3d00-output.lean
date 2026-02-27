/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b6629f07-b00d-4ff1-a5cf-8b39d14e3d00

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem SimpleGraph.IsTree.left_right_disjoint (h : G.IsTree) {u v : α} (huv : G.Adj u v) :
  h.leftPart u v ∩ h.rightPart u v = ∅

- theorem SimpleGraph.IsTree.left_union_right (h : G.IsTree) {u v : α} (huv : G.Adj u v) :
  h.leftPart u v ∪ h.rightPart u v = univ

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib
import Graphs.Separation


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

open Classical Set

variable {α : Type*} [Fintype α] {G : SimpleGraph α}

noncomputable def SimpleGraph.IsTree.thePath (h : G.IsTree) (u v : α) : G.Path u v := by
  choose p hp₁ hp₂ using h.existsUnique_path u v
  refine ⟨p, hp₁⟩

def SimpleGraph.IsTree.ordered (h : G.IsTree) (a b c : α) : Prop := b ∈ (h.thePath a c).1.support

def SimpleGraph.IsTree.leftPart (h : G.IsTree) (u v : α) : Set α := {w | h.ordered w u v}

def SimpleGraph.IsTree.rightPart (h : G.IsTree) (u v : α) : Set α := {w | h.ordered u v w}

noncomputable section AristotleLemmas

lemma SimpleGraph.IsTree.path_adj (h : G.IsTree) {u v : α} (huv : G.Adj u v) :
    (h.thePath u v).val = SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil := by
      -- Since u and v are adjacent, the unique path between them is the edge itself.
      have h_unique_path : ∀ p : G.Path u v, p = ⟨SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil, by
        aesop⟩ := by
        intro p
        generalize_proofs at *;
        have := h.existsUnique_path u v
        generalize_proofs at *;
        cases this ; aesop
      generalize_proofs at *;
      exact congr_arg Subtype.val ( h_unique_path _ )

lemma SimpleGraph.IsTree.path_split (h : G.IsTree) {u v w : α} (hv : v ∈ (h.thePath u w).val.support) :
    (h.thePath u w).val = (h.thePath u v).val.append (h.thePath v w).val := by
      have h_split : ∀ (p : G.Walk u w), v ∈ p.support → ∃ q : G.Walk u v, ∃ r : G.Walk v w, p = q.append r := by
        intro p hp;
        use p.takeUntil v hp;
        exact ⟨ p.dropUntil v hp, by simp +decide ⟩;
      obtain ⟨q, r, hp⟩ := h_split (h.thePath u w).1 hv
      have hq : q = (h.thePath u v).1 := by
        have := h.existsUnique_path u v;
        have hq : q.IsPath := by
          have hq : (h.thePath u w).1.IsPath := by
            exact ( h.thePath u w ).2
          generalize_proofs at *; (
          rw [ hp ] at hq; exact hq.of_append_left;)
        have hr : (h.thePath u v).1.IsPath := by
          grind
        have hq_eq : q = (h.thePath u v).1 := by
          exact ExistsUnique.unique ‹∃! p : G.Walk u v, p.IsPath› hq hr
        exact hq_eq.symm ▸ rfl
      have hr : r = (h.thePath v w).1 := by
        have := h.existsUnique_path v w;
        -- Since $r$ is a path from $v$ to $w$ and the tree's path from $v$ to $w$ is unique, they must be the same path.
        have hr_unique : r.IsPath := by
          have := (h.thePath u w).2;
          rw [hp] at this; exact this.of_append_right;
        exact this.unique hr_unique ( h.thePath v w |>.2 )
      rw [hp, hq, hr]

lemma SimpleGraph.IsTree.not_mem_of_adj_mem (h : G.IsTree) {u v w : α} (huv : G.Adj u v)
    (hw : v ∈ (h.thePath u w).val.support) : u ∉ (h.thePath v w).val.support := by
      -- Since the path from v to w is unique and does not contain u, we can conclude that u is not in the support of (h.thePath v w).
      have h_unique : ∀ p : G.Walk v w, p.IsPath → u ∉ p.support := by
        intro p hp hpu
        have h_unique : p = (h.thePath v w).val := by
          have := h.existsUnique_path v w; cases this; aesop;
        generalize_proofs at *; (
        have h_unique : (h.thePath u w).val = (huv).toWalk.append (h.thePath v w).val := by
          convert SimpleGraph.IsTree.path_split h hw using 1
          generalize_proofs at *; (
          rw [ SimpleGraph.IsTree.path_adj h huv ])
        generalize_proofs at *; (
        replace h_unique := congr_arg ( fun p => p.support ) h_unique ; simp_all +decide [ SimpleGraph.Walk.support_append ] ;
        have := h_unique.symm; simp_all +decide [ SimpleGraph.Walk.isPath_def ] ;
        replace this := congr_arg List.Nodup this ; simp_all +decide [ List.nodup_cons ] ;));
      exact h_unique _ ( h.thePath v w |>.2 )

end AristotleLemmas

theorem SimpleGraph.IsTree.left_right_disjoint (h : G.IsTree) {u v : α} (huv : G.Adj u v) :
  h.leftPart u v ∩ h.rightPart u v = ∅ := by
    -- Assume for contradiction that there exists a vertex `w` in both `leftPart` and `rightPart`.
    by_contra h_contra;
    simp_all +decide [ Set.ext_iff, SimpleGraph.IsTree.ordered ];
    obtain ⟨ w, hw₁, hw₂ ⟩ := h_contra;
    -- By definition of `leftPart` and `rightPart`, we have `v ∈ (h.thePath u w).val.support` and `u ∈ (h.thePath w v).val.support`.
    have hvw : v ∈ (h.thePath u w).val.support := by
      exact?
    have huw : u ∈ (h.thePath w v).val.support := by
      exact?;
    convert SimpleGraph.IsTree.not_mem_of_adj_mem h huv hvw using 1;
    simp +decide [ SimpleGraph.IsTree.path_split, SimpleGraph.IsTree.path_adj, huv ];
    have huw_rev : (h.thePath w v).val = (h.thePath v w).val.reverse := by
      have := h.existsUnique_path w v;
      refine' this.unique _ _ <;> aesop;
    aesop

theorem SimpleGraph.IsTree.left_union_right (h : G.IsTree) {u v : α} (huv : G.Adj u v) :
  h.leftPart u v ∪ h.rightPart u v = univ := by
    unfold SimpleGraph.IsTree.leftPart SimpleGraph.IsTree.rightPart
    ext w
    simp [SimpleGraph.IsTree.ordered];
    -- Since there's a unique path between any two vertices in a tree, if u is not in the path from w to v, then v must be in the path from u to w.
    have h_unique_path : ∀ u v w : α, ∃ p : G.Walk u w, p.IsPath := by
      -- By definition of IsTree, the graph is connected.
      have h_connected : G.Connected := by
        exact h.1;
      exact?;
    -- By the uniqueness of paths in a tree, if u is not in the path from w to v, then v must be in the path from u to w.
    by_cases hu : u ∈ (h.thePath w v).1.support;
    · exact Or.inl hu;
    · -- Since the path from u to w is unique and includes u and w, and we know that u is not in the path from w to v, it must be that the path from u to w includes v.
      have h_unique_path_uw : ∃ p : G.Walk u w, p.IsPath ∧ v ∈ p.support := by
        obtain ⟨p, hp⟩ : ∃ p : G.Walk w v, p.IsPath ∧ u∉p.support := by
          exact ⟨ _, h.thePath w v |>.2, hu ⟩
        generalize_proofs at *; (
        -- Since u and v are adjacent, we can create a path from u to w by taking the path from u to v and then appending the path from v to w.
        use SimpleGraph.Walk.cons huv p.reverse; simp [hp]);
      -- Since there's a unique path between any two vertices in a tree, if there's a path from u to w that includes v, then that path must be the same as the one from u to w.
      have h_unique_path_uw : ∀ p : G.Walk u w, p.IsPath → v ∈ p.support → v ∈ (h.thePath u w).1.support := by
        intros p hp hpv
        have h_unique_path_uw : p = (h.thePath u w).1 := by
          have := h.existsUnique_path u w
          generalize_proofs at *; (
          exact this.unique hp ( h.thePath u w |>.2 ) ▸ rfl)
        rw [h_unique_path_uw] at hpv
        exact hpv;
      grind +ring

structure TreeDecomposition (G : SimpleGraph α) where
  bags : Set (Set α)
  T : SimpleGraph bags
  --
  T_tree : T.IsTree
  union_bags : ⋃₀ bags = univ
  edge_mem_bag {u v : α} : G.Adj u v → ∃ b ∈ bags, {u, v} ⊆ b
  bag_inter {b₁ b₂ b₃ : bags} : T_tree.ordered b₁ b₂ b₃ → b₁.1 ∩ b₃.1 ⊆ b₂.1

namespace TreeDecomposition

variable {D : TreeDecomposition G}

noncomputable def width (D : TreeDecomposition G) : ℕ∞ := ⨆ b ∈ D.bags, Fintype.card b

/- Aristotle failed to find a proof. -/
lemma diestel_12_3_1 {b₁ b₂ : D.bags} (h : D.T.Adj b₁ b₂) :
    G.Separates (⋃₀ D.T_tree.leftPart b₁ b₂) (⋃₀ D.T_tree.rightPart b₁ b₂) (b₁ ∩ b₂) := by
  set U₁ : Set α := ⋃₀ D.T_tree.leftPart b₁ b₂
  set U₂ : Set α := ⋃₀ D.T_tree.rightPart b₁ b₂
  have h1 : U₁ ∪ U₂ = univ := by
    dsimp [U₁, U₂]
    rw [sUnion_eq_biUnion, sUnion_eq_biUnion, ← biUnion_union, ← image_union]
    rw [D.T_tree.left_union_right h, ← sUnion_eq_biUnion]
    simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq, D.union_bags]
  intro a ha b hb p
  -- Consider a shortest U1-U2 path. By (T1) it has length at most 1,
  -- so by (T2) it has length 0. By (T3), its vertex lies in Vt1 \ Vt2.
  sorry

end TreeDecomposition

noncomputable def treeWidth (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}