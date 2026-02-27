/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9f90fe12-0493-48a7-a6e7-bb18e7cb8812

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem left_right_ordered (huv : G.Adj u v) (ha : a ∈ h.left u v) (hb : b ∈ h.right u v) :
    h.ordered a u b ∧ h.ordered a v b

- theorem left_right_separates (huv : G.Adj u v) :
    G.Separates (h.left u v) (h.right u v) {u} ∧ G.Separates (h.left u v) (h.right u v) {v}

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

open Classical Set SimpleGraph

namespace SimpleGraph.IsTree

variable {α : Type*} {G : SimpleGraph α} {a b u v w : α} (h : G.IsTree)

noncomputable def path (u v : α) : G.Path u v := by
  choose p hp₁ hp₂ using h.existsUnique_path u v
  refine ⟨p, hp₁⟩

def ordered (a b c : α) : Prop := b ∈ (h.path a c).1.support

def left (u v : α) : Set α := {w | h.ordered w u v}

def right (u v : α) : Set α := {w | h.ordered u v w}

lemma path_adj (huv : G.Adj u v) : h.path u v = Walk.nil.cons huv := by
  have := h.existsUnique_path u v
  have h_unique_path : ∀ p : G.Path u v, p = ⟨Walk.cons huv Walk.nil, by aesop⟩ := by
    intro p
    generalize_proofs at *;
    cases this ; aesop
  exact congr_arg Subtype.val (h_unique_path _)

lemma path_split (hv : h.ordered u v w) : h.path u w = (h.path u v).1.append (h.path v w).1 := by
  have h_split : ∀ (p : G.Walk u w), v ∈ p.support → ∃ q : G.Walk u v, ∃ r : G.Walk v w, p = q.append r := by
    intro p hp;
    use p.takeUntil v hp;
    exact ⟨ p.dropUntil v hp, by simp +decide ⟩;
  obtain ⟨q, r, hp⟩ := h_split (h.path u w).1 hv
  have hq : q = (h.path u v).1 := by
    have := h.existsUnique_path u v;
    have hq : q.IsPath := by
      have hq : (h.path u w).1.IsPath := by
        exact ( h.path u w ).2
      generalize_proofs at *; (
      rw [ hp ] at hq; exact hq.of_append_left;)
    have hr : (h.path u v).1.IsPath := by
      grind
    have hq_eq : q = (h.path u v).1 := by
      exact ExistsUnique.unique ‹∃! p : G.Walk u v, p.IsPath› hq hr
    exact hq_eq.symm ▸ rfl
  have hr : r = (h.path v w).1 := by
    have := h.existsUnique_path v w;
    -- Since $r$ is a path from $v$ to $w$ and the tree's path from $v$ to $w$ is unique, they must be the same path.
    have hr_unique : r.IsPath := by
      have := (h.path u w).2;
      rw [hp] at this; exact this.of_append_right;
    exact this.unique hr_unique ( h.path v w |>.2 )
  rw [hp, hq, hr]

lemma not_mem_of_adj_mem (huv : G.Adj u v) (hw : h.ordered u v w) : u ∉ (h.path v w).1.support := by
  have h_unique : ∀ p : G.Walk v w, p.IsPath → u ∉ p.support := by
    intro p hp hpu
    have h_unique : p = (h.path v w).val := by
      have := h.existsUnique_path v w; cases this; aesop;
    generalize_proofs at *; (
    have h_unique : (h.path u w).val = (huv).toWalk.append (h.path v w).val := by
      convert path_split h hw using 1
      generalize_proofs at *; (
      rw [ path_adj h huv ])
    generalize_proofs at *; (
    replace h_unique := congr_arg ( fun p => p.support ) h_unique ; simp_all +decide [ Walk.support_append ] ;
    have := h_unique.symm; simp_all +decide [ Walk.isPath_def ] ;
    replace this := congr_arg List.Nodup this ; simp_all +decide [ List.nodup_cons ] ;));
  exact h_unique _ ( h.path v w |>.2 )

theorem left_right_disjoint (huv : G.Adj u v) : h.left u v ∩ h.right u v = ∅ := by
    -- Assume for contradiction that there exists a vertex `w` in both `leftPart` and `rightPart`.
    by_contra h_contra;
    simp_all +decide [ Set.ext_iff, ordered ];
    obtain ⟨ w, hw₁, hw₂ ⟩ := h_contra;
    -- By definition of `leftPart` and `rightPart`, we have `v ∈ (h.thePath u w).val.support` and `u ∈ (h.thePath w v).val.support`.
    have hvw : v ∈ (h.path u w).val.support := by exact?
    have huw : u ∈ (h.path w v).val.support := by exact?;
    convert not_mem_of_adj_mem h huv hvw using 1;
    simp +decide [ path_split, path_adj, huv ];
    have huw_rev : (h.path w v).val = (h.path v w).val.reverse := by
      have := h.existsUnique_path w v;
      refine' this.unique _ _ <;> aesop;
    aesop

theorem left_union_right (huv : G.Adj u v) : h.left u v ∪ h.right u v = univ := by
    unfold left right
    ext w
    simp [ordered];
    -- Since there's a unique path between any two vertices in a tree, if u is not in the path from w to v, then v must be in the path from u to w.
    have h_unique_path : ∀ u v w : α, ∃ p : G.Walk u w, p.IsPath := by
      -- By definition of IsTree, the graph is connected.
      have h_connected : G.Connected := by
        exact h.1;
      exact?;
    -- By the uniqueness of paths in a tree, if u is not in the path from w to v, then v must be in the path from u to w.
    by_cases hu : u ∈ (h.path w v).1.support;
    · exact Or.inl hu;
    · -- Since the path from u to w is unique and includes u and w, and we know that u is not in the path from w to v, it must be that the path from u to w includes v.
      have h_unique_path_uw : ∃ p : G.Walk u w, p.IsPath ∧ v ∈ p.support := by
        obtain ⟨p, hp⟩ : ∃ p : G.Walk w v, p.IsPath ∧ u∉p.support := by
          exact ⟨ _, h.path w v |>.2, hu ⟩
        generalize_proofs at *; (
        -- Since u and v are adjacent, we can create a path from u to w by taking the path from u to v and then appending the path from v to w.
        use Walk.cons huv p.reverse; simp [hp]);
      -- Since there's a unique path between any two vertices in a tree, if there's a path from u to w that includes v, then that path must be the same as the one from u to w.
      have h_unique_path_uw : ∀ p : G.Walk u w, p.IsPath → v ∈ p.support → v ∈ (h.path u w).1.support := by
        intros p hp hpv
        have h_unique_path_uw : p = (h.path u w).1 := by
          have := h.existsUnique_path u w
          generalize_proofs at *; (
          exact this.unique hp ( h.path u w |>.2 ) ▸ rfl)
        rw [h_unique_path_uw] at hpv
        exact hpv;
      grind +ring

noncomputable section AristotleLemmas

/-
If a is in the left set of u v (meaning u is on the path from a to v), and x is on the path from a to u, then x is also in the left set (meaning u is on the path from x to v).
-/
lemma path_mem_left (huv : G.Adj u v) (ha : a ∈ h.left u v) {x : α} (hx : x ∈ (h.path a u).1.support) : x ∈ h.left u v := by
  have hx_left : h.path a v = (h.path a x).1.append (h.path x v).1 := by
    apply h.path_split; exact (by
    have h_ordered : h.path a v = (h.path a u).1.append (h.path u v).1 := by
      convert h.path_split ha using 1;
    unfold SimpleGraph.IsTree.ordered at *; aesop;)
  have hx_left' : h.path a u = (h.path a x).1.append (h.path x u).1 := by
    convert h.path_split _ using 1 ; aesop;
  have hx_support : x ∈ (h.path x v).1.support := by
    simp +decide [ SimpleGraph.Walk.support ];
  have hx_support : u ∈ (h.path a v).1.support := by
    exact?;
  have hx_support : u ∈ (h.path a x).1.support ∨ u ∈ (h.path x v).1.support := by
    aesop;
  cases hx_support <;> simp_all +decide [ SimpleGraph.IsTree.ordered ];
  · have hx_support : h.path a x = (h.path a u).1.append (h.path u x).1 := by
      apply path_split;
      exact?;
    have := congr_arg SimpleGraph.Walk.length hx_support; norm_num at this;
    rw [ hx_left' ] at this ; simp +decide at this;
    simp +decide [ add_assoc ] at this;
    cases h : ( h.path x u : G.Walk x u ) <;> simp +decide [ h ] at this ⊢;
    simp +decide [ SimpleGraph.IsTree.left ] at *;
    simp +decide [ SimpleGraph.IsTree.ordered ] at *;
  · have := h.left_right_disjoint huv; simp_all +decide [ Set.ext_iff ] ;
    specialize this u ; aesop

/-
If b is in the right set of u v (meaning v is on the path from u to b), and x is on the path from v to b, then x is also in the right set (meaning v is on the path from u to x).
-/
lemma path_mem_right (huv : G.Adj u v) (hb : b ∈ h.right u v) {x : α} (hx : x ∈ (h.path v b).1.support) : x ∈ h.right u v := by
  -- By definition of $h.path$, we know that $x$ is on the path from $v$ to $b$.
  have h_append : (h.path v b).1 = (h.path v x).1.append (h.path x b).1 := by
    convert h.path_split _ using 1 ; aesop;
  -- By definition of $h.path$, we know that $x$ is on the path from $u$ to $b$.
  have h_append : (h.path u b).1 = (h.path u v).1.append ((h.path v x).1.append (h.path x b).1) := by
    rw [ ← h_append, ← path_split ] ; aesop;
  unfold SimpleGraph.IsTree.right at *;
  unfold SimpleGraph.IsTree.ordered at *; simp_all +decide [ SimpleGraph.Walk.bypass ] ;
  have h_append : (h.path u x).1 = (h.path u v).1.append (h.path v x).1 := by
    have h_unique : ∀ p q : G.Walk u x, p.IsPath → q.IsPath → p = q := by
      have := h.existsUnique_path u x;
      exact fun p q hp hq => this.unique hp hq
    apply h_unique;
    · exact h.path u x |>.2;
    · have h_append : (h.path u b).1.IsPath := by
        exact h.path u b |>.2;
      simp_all +decide [ SimpleGraph.Walk.isPath_def ];
      simp_all +decide [ SimpleGraph.Walk.support_append ];
      exact h_append.sublist ( by simp +decide [ List.sublist_append_right ] );
  aesop

/-
If a is in the left set and b is in the right set of an edge uv, then the path from a to b is the concatenation of the path from a to u, the edge uv, and the path from v to b.
-/
lemma path_eq_append_of_adj (huv : G.Adj u v) (ha : a ∈ h.left u v) (hb : b ∈ h.right u v) : (h.path a b).1 = (h.path a u).1.append ((h.path u v).1.append (h.path v b).1) := by
  obtain ⟨ p₁, hp₁ ⟩ := h.existsUnique_path a b;
  obtain ⟨ p₂, hp₂ ⟩ := h.existsUnique_path a u
  obtain ⟨ p₃, hp₃ ⟩ := h.existsUnique_path v b
  have h_path : p₁ = p₂.append (SimpleGraph.Walk.cons huv p₃) := by
    refine' hp₁.2 _ _ ▸ rfl;
    simp_all +decide [ SimpleGraph.Walk.isPath_def ];
    simp_all +decide [ SimpleGraph.Walk.support_append, List.nodup_append ];
    intro x hx y hy hxy;
    have h_contradiction : x ∈ (h.path a u).1.support ∧ x ∈ (h.path v b).1.support := by
      aesop;
    have h_contradiction : x ∈ h.left u v ∧ x ∈ h.right u v := by
      exact ⟨ path_mem_left h huv ha h_contradiction.1, path_mem_right h huv hb h_contradiction.2 ⟩;
    exact absurd ( left_right_disjoint h huv ) ( Set.Nonempty.ne_empty ⟨ x, h_contradiction ⟩ );
  have h_path_eq : h.path a b = p₁ ∧ h.path a u = p₂ ∧ h.path v b = p₃ ∧ h.path u v = SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil := by
    refine' ⟨ _, _, _, _ ⟩;
    · exact hp₁.2 _ ( h.path a b |>.2 );
    · exact hp₂.2 _ ( h.path a u |>.2 );
    · exact hp₃.2 _ ( h.path v b |>.2 );
    · convert path_adj h huv;
  aesop

end AristotleLemmas

theorem left_right_ordered (huv : G.Adj u v) (ha : a ∈ h.left u v) (hb : b ∈ h.right u v) :
    h.ordered a u b ∧ h.ordered a v b := by
  -- By `path_eq_append_of_adj`, the path from `a` to `b` is the concatenation of the path from `a` to `u`, the edge `uv`, and the path from `v` to `b`. Thus, the support of the path from `a` to `b` contains the support of the path from `a` to `u` (which contains `u`) and the support of the path from `v` to `b` (which contains `v`).
  have h_support : (h.path a b).1.support.contains u ∧ (h.path a b).1.support.contains v := by
    rw [ path_eq_append_of_adj ];
    any_goals assumption;
    aesop;
  aesop

theorem left_right_separates (huv : G.Adj u v) :
    G.Separates (h.left u v) (h.right u v) {u} ∧ G.Separates (h.left u v) (h.right u v) {v} := by
  constructor <;> intro a ha b hb p;
  · have := h.left_right_ordered huv ha hb;
    have h_unique_path : ∀ p q : G.Walk a b, p.IsPath → q.IsPath → p = q := by
      have := h.existsUnique_path a b;
      exact fun p q hp hq => this.unique hp hq;
    -- Since p is a walk, we can find a subwalk that is a path.
    obtain ⟨q, hq⟩ : ∃ q : G.Walk a b, q.IsPath ∧ q.support ⊆ p.support := by
      have h_subwalk : ∀ p : G.Walk a b, ∃ q : G.Walk a b, q.IsPath ∧ q.support ⊆ p.support := by
        intro p
        obtain ⟨q, hq⟩ : ∃ q : G.Walk a b, q.IsPath ∧ q.support ⊆ p.support := by
          have h_walk : ∀ p : G.Walk a b, ∃ q : G.Walk a b, q.IsPath ∧ q.support ⊆ p.support := by
            intro p
            exact ⟨p.toPath, by
              grind, by
              -- Since $p.toPath$ is a path, its support is a subset of $p$'s support.
              apply SimpleGraph.Walk.support_toPath_subset⟩
          exact h_walk p;
        use q;
      exact h_subwalk p;
    specialize h_unique_path q ( h.path a b ) ; aesop;
  · -- Since p is a path from a to b and v is ordered between a and b, v must be in the support of p.
    have h_v_in_support : v ∈ p.support := by
      -- Since $p$ is a walk from $a$ to $b$, and $a$ is in the left set and $b$ is in the right set, the path from $a$ to $b$ must pass through $v$.
      have h_path : v ∈ (h.path a b).1.support := by
        have := h.left_right_ordered huv ha hb;
        exact this.2;
      have h_unique_path : ∀ p q : G.Walk a b, p.IsPath → q.IsPath → p = q := by
        -- Since G is a tree, there is a unique path between any two vertices. Therefore, any two paths between a and b must be equal.
        have h_unique_path : ∀ p q : G.Walk a b, p.IsPath → q.IsPath → p = q := by
          intro p q hp hq
          have h_unique : ∃! p : G.Walk a b, p.IsPath := by
            exact h.existsUnique_path a b
          exact h_unique.unique hp hq;
        exact h_unique_path;
      contrapose! h_unique_path;
      refine' ⟨ p.toPath, h.path a b, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.isPath_def ];
      intro h_eq; simp_all +decide [ SimpleGraph.Walk.toPath ] ;
      replace h_eq := congr_arg ( fun q => v ∈ q.support ) h_eq ; simp_all +decide [ SimpleGraph.Walk.bypass ] ;
      exact h_unique_path ( by simpa using SimpleGraph.Walk.support_bypass_subset _ h_eq );
    aesop

end SimpleGraph.IsTree