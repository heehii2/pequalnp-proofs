import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first three premises are the deletion bounds L-meta-2012, L-meta-2036, and L-meta-1664.
-- The last rules out a finite family of minimum circuits, allowing either output polarity.
-- In the Petersen graph row i lists the larger neighbors of vertex i. Each edge occurs once.
-- In the restricted circuit, count the signed target only if it contributes a new signal.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 14000000 in
theorem PEqualNP.Outside.R_meta_2371_683
    (lower9 : let f := (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun d => x (Fin.ofNat 9 (d / 10)) && x (Fin.ofNat 9 (d % 10))))
      ¬ HasCircuitSize 9 f 14)
    (lowerA : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) ||
      (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (lowerB : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 5 && x 7)) 11)
    (residual : let Vertex := Fin 10
      let Assignment := Vertex → Bool
      ∀ (C : Circuit) (b : Bool),
      let E (i j : Vertex) :=
        (([[1, 4, 5], [2, 6], [3, 7], [4, 8], [9],
           [7, 8], [8, 9], [9], [], []] : List (List ℕ)).getD
          (min i.val j.val) []).contains (max i.val j.val)
      let D : Circuit := ⟨C.gates ++ [⟨if b then .not else .or,[C.output]⟩],10+C.size⟩
      let count (B : Circuit) (r : Assignment → Assignment) :=
        let w (j : ℕ) (x : Assignment) := (B.wires (List.ofFn (r x))).getD j false
        ((Finset.range (10+B.size)).image w \ insert (fun _ => false) ((Finset.range 10).image w)).card
      FanInTwo C → C.size ≤ 18 → C.output = 9+C.size →
      (∀ i ∈ C.gates.flatMap Gate.inputs, i ≤ 28) → C.size ≤ count C id →
      (b = true → 2 ≤ C.gates.countP (fun h => h.op.eval [false,false])) →
      (∀ (u v a d : Vertex) (s t : Bool), E a d = true →
        (if u=v then 15 else if E u v then 13 else 12) ≤ (if s || t then 1 else 0) +
          count D (fun x i => if i = u ∨ i = v then
            (if i = u then s else t) && (x a && x d) else x i)) →
      ¬ ∀ x : Assignment, D.eval (List.ofFn x) = decide (∃ i j, E i j = true ∧ x i = true ∧ x j = true))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         ∃ (x10 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x9 x10 x3 else x9 x10 x3) ≠ x8 x10 := by
  have petExtend (n m : ℕ) (L : List Gate) (seed : (Fin n → Bool) → List Bool)
      (len : ∀ x, (seed x).length = m)
      (B0 : Circuit) (baseFan : FanInTwo B0)
      (initial : ∀ j : ℕ, ∃ k : ℕ, ∀ x : Fin n → Bool,
        (B0.wires (List.ofFn x)).getD k false = (seed x).getD j false)
      (fan : FanInTwo ⟨L,0⟩) (o : ℕ) :
      let w (j : ℕ) (x : Fin n → Bool) := ((⟨L,0⟩ : Circuit).wires (seed x)).getD j false
      let A := (Finset.range (m + L.length)).image w
      let B := insert (fun _ : Fin n → Bool => false) ((Finset.range m).image w)
      HasCircuitSize n (w o) (B0.size + (A \ B).card) := by
    clear lower9 lowerA lowerB residual
    classical
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have ext (xs : List Gate) (u : List Bool) : ∃ v, xs.foldl step u = u ++ v := by
      induction xs generalizing u with
      | nil => exact ⟨[],by simp⟩
      | cons a xs ih =>
        obtain ⟨t,h⟩ := ih (step u a)
        exact ⟨[_] ++ t,by simpa [step,List.foldl_cons,List.append_assoc] using h⟩
    have lens (xs : List Gate) (u : List Bool) : (xs.foldl step u).length = u.length + xs.length := by
      induction xs generalizing u with
      | nil => simp
      | cons a xs ih => rw [List.foldl_cons,ih]; simp [step]; omega
    have snocNe (u : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ u.length) :
        (u ++ [b]).getD i false = u.getD i false := by
      by_cases h : i < u.length
      · exact List.getD_append _ _ _ _ h
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
    have snocEq (u : List Bool) (b : Bool) : (u ++ [b]).getD u.length false = b := by simp
    let Z := fun _ : Fin n → Bool => false
    let V (xs : List Gate) (j : ℕ) (x : Fin n → Bool) := (xs.foldl step (seed x)).getD j false
    let val (xs : List Gate) (g : Gate) (x : Fin n → Bool) := g.op.eval (g.inputs.map fun i => V xs i x)
    let pool (xs : List Gate) := (Finset.range (m+xs.length)).image (V xs)
    let basis := insert Z ((Finset.range m).image (V []))
    let fresh (xs : List Gate) := pool xs \ basis
    have preserve (xs : List Gate) (i : ℕ) (hi : i < m) : V xs i = V [] i := by
      funext x
      obtain ⟨v,hv⟩ := ext xs (seed x)
      change (xs.foldl step (seed x)).getD i false = (seed x).getD i false
      rw [hv,List.getD_append _ _ _ _ (by rwa [len])]
    have far (xs : List Gate) : V xs (m+xs.length) = Z := by
      funext x
      change (xs.foldl step (seed x)).getD _ false = false
      apply List.getD_eq_default
      rw [lens,len]
    have next (xs : List Gate) (g : Gate) (i : ℕ) :
        V (xs ++ [g]) i = if i = m+xs.length then val xs g else V xs i := by
      funext x
      change ((xs ++ [g]).foldl step (seed x)).getD i false = _
      rw [List.foldl_append]
      change ((xs.foldl step (seed x)) ++ [val xs g x]).getD i false = _
      by_cases h : i = m+xs.length
      · rw [ite_eq_left h]
        have e : i = (xs.foldl step (seed x)).length := by rw [lens,len,h]
        rw [e,snocEq]
      · rw [ite_eq_right h]
        apply snocNe
        rwa [lens,len]
    have build (xs : List Gate) (ok : FanInTwo ⟨xs,0⟩) :
        ∃ D : Circuit, FanInTwo D ∧ D.size ≤ B0.size + (fresh xs).card ∧
        ∀ i : ℕ, ∃ j : ℕ, ∀ x : Fin n → Bool,
          (D.wires (List.ofFn x)).getD j false = V xs i x := by
      induction xs using List.reverseRecOn with
      | nil =>
        exact ⟨B0,baseFan,Nat.le_add_right _ _,initial⟩
      | append_singleton xs g ih =>
        obtain ⟨D,hm,hs,links⟩ := ih (fun a ha => ok a (List.mem_append_left _ ha))
        choose idx hidx using links
        have oldSub : fresh xs ⊆ fresh (xs ++ [g]) := by
          intro f hf
          obtain ⟨hpool,hb⟩ := Finset.mem_sdiff.mp hf
          obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hpool
          have lt := Finset.mem_range.mp hi
          apply Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by simp; omega),?_⟩,hb⟩
          rw [next,ite_eq_right (Nat.ne_of_lt lt)]
        have covered (hc : val xs g ∈ pool xs ∨ val xs g ∈ basis) :
            ∃ j, ∀ x, (D.wires (List.ofFn x)).getD j false = val xs g x := by
          rcases hc with h | h
          · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
            exact ⟨idx i,fun x => (hidx i x).trans (congrFun hi x)⟩
          · rcases Finset.mem_insert.mp h with hz | h
            · exact ⟨idx (m+xs.length),fun x => (hidx _ x).trans (congrFun ((far xs).trans hz.symm) x)⟩
            · obtain ⟨i,hi,e⟩ := Finset.mem_image.mp h
              exact ⟨idx i,fun x => (hidx _ x).trans (congrFun ((preserve xs i (Finset.mem_range.mp hi)).trans e) x)⟩
        by_cases already : val xs g ∈ pool xs ∨ val xs g ∈ basis
        · obtain ⟨j,hj⟩ := covered already
          refine ⟨D,hm,hs.trans (Nat.add_le_add_left (Finset.card_le_card oldSub) _),?_⟩
          intro i
          by_cases e : i = m+xs.length
          · exact ⟨j,fun x => (hj x).trans (congrFun ((next xs g i).trans (ite_eq_left e)).symm x)⟩
          · exact ⟨idx i,fun x => (hidx i x).trans (congrFun ((next xs g i).trans (ite_eq_right e)).symm x)⟩
        · have vnew : val xs g ∈ fresh (xs++[g]) := by
            refine Finset.mem_sdiff.mpr ⟨?_,fun h => already (Or.inr h)⟩
            apply Finset.mem_image.mpr
            exact ⟨m+xs.length,Finset.mem_range.mpr (by simp),(next _ _ _).trans (ite_eq_left rfl)⟩
          have inc : (fresh xs).card < (fresh (xs++[g])).card := by
            apply Finset.card_lt_card
            exact Finset.ssubset_iff_of_subset oldSub |>.mpr ⟨_,vnew,fun h => already (.inl (Finset.mem_sdiff.mp h).1)⟩
          let a : Gate := ⟨g.op,g.inputs.map idx⟩
          let D' : Circuit := ⟨D.gates ++ [a],0⟩
          have strong (x : Fin n → Bool) : D'.wires (List.ofFn x) =
              D.wires (List.ofFn x) ++ [val xs g x] := by
            change ((D.gates ++ [a]).foldl step (List.ofFn x)) = _
            rw [List.foldl_append]
            change D.wires (List.ofFn x) ++ [g.op.eval ((g.inputs.map idx).map _)] = _
            simp only [List.map_map]
            congr 3
            apply List.map_congr_left
            intro i _
            exact hidx i x
          have ld (x : Fin n → Bool) : (D.wires (List.ofFn x)).length = n+D.size := by
            change (D.gates.foldl step (List.ofFn x)).length = _
            rw [lens,List.length_ofFn]
            rfl
          refine ⟨D',?_,?_,?_⟩
          · intro b hb
            change b ∈ D.gates ++ [a] at hb
            rcases List.mem_append.mp hb with p | p
            · exact hm b p
            · obtain rfl := List.mem_singleton.mp p
              have ha := ok g (List.mem_append_right xs (List.mem_singleton_self _))
              exact ⟨ha.1,by simpa [a] using ha.2⟩
          · change (D.gates++[a]).length ≤ _
            change D.gates.length ≤ _ at hs
            simp only [List.length_append,List.length_singleton]
            omega
          · intro i
            by_cases h : i = m+xs.length
            · refine ⟨n+D.size,fun x => ?_⟩
              rw [strong,← ld x,snocEq,next,ite_eq_left h]
            · by_cases b : idx i = n+D.size
              · refine ⟨n+D.size+1,fun x => ?_⟩
                rw [strong,List.getD_eq_default _ _ (by simp [ld]),next,ite_eq_right h,← hidx i x,b]
                exact (List.getD_eq_default _ _ (by rw [ld])).symm
              · refine ⟨idx i,fun x => ?_⟩
                rw [strong,snocNe _ _ _ (by rwa [ld]),next,ite_eq_right h]
                exact hidx i x
    obtain ⟨D,hm,hs,bind⟩ := build L fan
    obtain ⟨j,res⟩ := bind o
    have basisL : (Finset.range m).image (V L) = (Finset.range m).image (V []) := by
      apply Finset.image_congr
      intro i hi
      exact preserve L i (Finset.mem_range.mp hi)
    refine ⟨⟨D.gates,j⟩,hm,?_,res⟩
    change D.size ≤ B0.size + (pool L \ insert Z ((Finset.range m).image (V L))).card
    rw [basisL]
    exact hs

  have pet2371Seed (n : ℕ) (lift : (Fin n → Bool) → Fin 10 → Bool)
      (axes : ∀ j, (∀ x, lift x j = false) ∨ ∃ i : Fin n, ∀ x, lift x j = x i)
      (u v a d : Fin 10) (s t : Bool) :
      let raw (x : Fin 10 → Bool) (i : Fin 10) :=
        if i = u ∨ i = v then (if i = u then s else t) && (x a && x d) else x i
      ∃ B : Circuit, FanInTwo B ∧ B.size ≤ (if s || t then 1 else 0) ∧
        ∀ j : ℕ, ∃ k : ℕ, ∀ x : Fin n → Bool,
          (B.wires (List.ofFn x)).getD k false = (List.ofFn (raw (lift x))).getD j false := by
    clear lower9 lowerA lowerB residual petExtend
    intro raw
    classical
    have pick (j : Fin 10) : ∃ k : ℕ, k ≠ n ∧ ∀ x : Fin n → Bool, (List.ofFn x).getD k false = lift x j := by
      rcases axes j with h | ⟨i,h⟩
      · exact ⟨n+1,by omega,fun x => by rw [h]; simp⟩
      · exact ⟨i.val,Nat.ne_of_lt i.isLt,fun x => by rw [h]; simp⟩
    choose idx safe lookup using pick
    let g : Gate := ⟨.and,[idx a,idx d]⟩
    let B : Circuit := ⟨if s || t then [g] else [],n⟩
    have fan : FanInTwo B := by
      intro h hh
      change h ∈ (if s || t then [g] else []) at hh
      split at hh
      · obtain rfl := List.mem_singleton.mp hh
        exact ⟨Or.inl rfl,Nat.le_refl 2⟩
      · cases hh
    have size : B.size ≤ (if s || t then 1 else 0) := by
      change (if s || t then [g] else []).length ≤ _
      split <;> exact le_rfl
    have conj (c e : Bool) : GateOp.and.eval [c,e] = (c && e) := by cases c <;> cases e <;> rfl
    have state (x : Fin n → Bool) : B.wires (List.ofFn x) =
        List.ofFn x ++ (if s || t then [lift x a && lift x d] else []) := by
      change (if s || t then [g] else []).foldl _ (List.ofFn x) = _
      split
      · change List.ofFn x ++ [GateOp.and.eval [(List.ofFn x).getD (idx a) false,(List.ofFn x).getD (idx d) false]] = _
        rw [conj,lookup,lookup]
      · simp
    have zero (x : Fin n → Bool) : (B.wires (List.ofFn x)).getD (n+1) false = false := by
      rw [state]
      apply List.getD_eq_default
      split <;> simp
    have before (x : Fin n → Bool) (i : Fin 10) : (B.wires (List.ofFn x)).getD (idx i) false = lift x i := by
      rw [state]
      by_cases hi : idx i < n
      · rw [List.getD_append _ _ _ _ (by simpa using hi),lookup]
      · have hn := safe i
        rw [← lookup i x,List.getD_eq_default (List.ofFn x) _ (by simp; omega)]
        apply List.getD_eq_default
        split <;> simp <;> omega
    have active (x : Fin n → Bool) (h : (s || t) = true) :
        (B.wires (List.ofFn x)).getD n false = (lift x a && lift x d) := by
      rw [state,ite_eq_left h]
      simpa using (List.getD_append_right (List.ofFn x) [lift x a && lift x d] n false (by simp))
    refine ⟨B,fan,size,?_⟩
    intro j
    by_cases hj : j < 10
    · let i : Fin 10 := ⟨j,hj⟩
      have atRaw (x) : (List.ofFn (raw (lift x))).getD j false = raw (lift x) i := by
        rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_ofFn]
      by_cases hidden : i = u ∨ i = v
      · by_cases flag : (if i = u then s else t) = true
        · have yes : (s || t) = true := by split at flag <;> simp [flag]
          refine ⟨n,fun x => ?_⟩
          rw [atRaw,active x yes]
          simp [raw,hidden,flag]
        · have off := Bool.eq_false_iff.mpr flag
          refine ⟨n+1,fun x => ?_⟩
          rw [atRaw,zero]
          simp [raw,hidden,off]
      · refine ⟨idx i,fun x => ?_⟩
        rw [atRaw,before]
        simp [raw,hidden]
    · refine ⟨n+1,fun x => ?_⟩
      rw [zero,List.getD_eq_default _ _ (by simp; omega)]

  have pet2371Graph :
      let F := (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
      (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) ||
      (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      let E (i j : Fin 10) :=
        (([[1, 4, 5], [2, 6], [3, 7], [4, 8], [9],
           [7, 8], [8, 9], [9], [], []] : List (List ℕ)).getD
          (min i.val j.val) []).contains (max i.val j.val)
      (∀ x : Fin 10 → Bool, F x = decide (∃ i j, E i j = true ∧ x i = true ∧ x j = true)) ∧
      (∀ u v : Fin 10, E u v = F (fun i => decide (i = u ∨ i = v))) := by
    clear lower9 lowerA lowerB residual petExtend pet2371Seed
    intro F E
    let edges : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
      (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
    have same (x : Fin 10 → Bool) : F x = edges.any (fun p => x p.1 && x p.2) := by
      simp only [F,edges,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    have elist : ∀ i j : Fin 10, E i j = true ↔ (i,j) ∈ edges ∨ (j,i) ∈ edges := by decide
    constructor
    · intro x
      apply Bool.eq_iff_iff.mpr
      rw [same]
      constructor
      · intro ox
        obtain ⟨⟨i,j⟩,mem,h⟩ := List.any_eq_true.mp ox
        have h' := Bool.and_eq_true_iff.mp h
        exact decide_eq_true ⟨i,j,(elist i j).mpr (.inl mem),h'.1,h'.2⟩
      · intro ht
        obtain ⟨i,j,h,xi,xj⟩ := of_decide_eq_true ht
        apply List.any_eq_true.mpr
        rcases (elist i j).mp h with d | d
        · exact ⟨(i,j),d,Bool.and_eq_true_iff.mpr ⟨xi,xj⟩⟩
        · exact ⟨(j,i),d,Bool.and_eq_true_iff.mpr ⟨xj,xi⟩⟩
    · decide +kernel

  have pet2371Deck :
    let F (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
      (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) ||
      (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
    let standard (y : Fin 9 → Bool) :=
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun d => y (Fin.ofNat 9 (d / 10)) && y (Fin.ofNat 9 (d % 10)))
    let f2036 (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) ||
      (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
    let f1664 (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 5 && x 7)
    let adj (u v : Fin 10) := F (fun i => decide (i = u ∨ i = v))
    (∀ u : Fin 10, ∃ lift : (Fin 9 → Bool) → Fin 10 → Bool,
      (∀ x, lift x u = false) ∧
      (∀ j, (∀ x, lift x j = false) ∨ ∃ i : Fin 9, ∀ x, lift x j = x i) ∧
      (∀ x, F (lift x) = standard x)) ∧
    (∀ u v : Fin 10, u ≠ v → ∃ lift : (Fin 8 → Bool) → Fin 10 → Bool,
      (∀ x, lift x u = false ∧ lift x v = false) ∧
      (∀ j, (∀ x, lift x j = false) ∨ ∃ i : Fin 8, ∀ x, lift x j = x i) ∧
      (∀ x, F (lift x) = if adj u v then f2036 x else f1664 x)) := by
    clear lower9 lowerA lowerB residual petExtend pet2371Seed pet2371Graph
    intro F standard f2036 f1664 adj
    let first : List (List ℕ) :=
      [[9,4,0,1,6,7,3,5,2,8],
       [4,9,6,1,0,3,7,8,2,5],
       [0,4,9,6,1,5,3,7,8,2],
       [0,1,6,9,4,5,2,8,7,3],
       [4,0,1,6,9,3,5,2,8,7],
       [4,0,1,2,3,9,5,6,7,8],
       [0,4,3,2,1,5,9,8,7,6],
       [0,1,6,8,5,4,2,9,3,7],
       [0,1,2,7,5,4,6,3,9,8],
       [0,1,2,3,4,5,6,7,8,9]]
    let src9 (u j : Fin 10) := (first.getD u.val []).getD j.val 9
    let firstLift (u : Fin 10) (x : Fin 9 → Bool) (j : Fin 10) :=
      if h : src9 u j < 9 then x ⟨src9 u j,h⟩ else false
    have gone : ∀ u : Fin 10, src9 u u = 9 := by decide
    have kept : ∀ u v : Fin 10, u ≠ v → src9 u v < 9 := by decide
    have incidence : ∀ u v : Fin 10, u ≠ v →
        (src9 u v ∈ ([4,6,7] : List ℕ) ↔ adj u v = true) := by decide
    have table : ∀ (u : Fin 10) (x : Fin 9 → Bool), F (firstLift u x) = standard x := by
      decide +kernel
    have zero (u : Fin 10) (x : Fin 9 → Bool) : firstLift u x u = false := by
      simp only [firstLift,gone]
      rfl
    have axes (u j : Fin 10) : (∀ x, firstLift u x j = false) ∨ ∃ i : Fin 9, ∀ x, firstLift u x j = x i := by
      by_cases h : src9 u j < 9
      · exact Or.inr ⟨⟨_,h⟩,fun x => by simp only [firstLift,dite_eq_left h]⟩
      · exact Or.inl (fun x => by simp only [firstLift,dite_eq_right h])
    let deck : List (List ℕ) :=
      [[8,7,3,2,6,0,5,4,1],
       [0,8,7,3,4,1,6,5,2],
       [1,0,8,7,5,2,4,6,3],
       [2,1,0,8,6,3,5,4,7],
       [0,1,2,3,8,4,5,6,7],
       [0,1,2,3,4,8,5,6,7],
       [1,0,4,7,5,2,8,6,3],
       [2,1,5,7,3,6,0,8,4],
       [1,2,3,7,5,0,6,4,8]]
    let src (v j : Fin 9) := (deck.getD v.val []).getD j.val 8
    let lift (v : Fin 9) (x : Fin 8 → Bool) (j : Fin 9) :=
      if h : src v j < 8 then x ⟨src v j,h⟩ else false
    have missing : ∀ v : Fin 9, src v v = 8 := by decide
    have cofactor : ∀ (v : Fin 9) (x : Fin 8 → Bool), standard (lift v x) =
        if v.val ∈ ([4,6,7] : List ℕ) then f2036 x else f1664 x := by
      decide +kernel
    refine ⟨fun u => ⟨firstLift u,zero u,axes u,table u⟩,?_⟩
    intro u v diff
    let j : Fin 9 := ⟨src9 u v,kept u v diff⟩
    let pairLift (x : Fin 8 → Bool) := firstLift u (lift j x)
    refine ⟨pairLift,?_,?_,?_⟩
    · intro x
      refine ⟨zero _ _,?_⟩
      change firstLift u (lift j x) v = false
      have atV : lift j x j = false := by simp only [lift,missing]; rfl
      simpa only [firstLift,dite_eq_left (kept u v diff)] using atV
    · intro i
      rcases axes u i with off | ⟨l,h⟩
      · exact Or.inl (fun x => off (lift j x))
      by_cases ok : src j l < 8
      · refine Or.inr ⟨⟨_,ok⟩,fun x => (h (lift j x)).trans ?_⟩
        simp only [lift,dite_eq_left ok]
      · refine Or.inl (fun x => (h (lift j x)).trans ?_)
        simp only [lift,dite_eq_right ok]
    · intro x
      change F (firstLift u (lift j x)) = _
      rw [table,cofactor]
      change (if src9 u v ∈ ([4,6,7] : List ℕ) then f2036 x else f1664 x) = _
      by_cases h : adj u v = true
      · rw [ite_eq_left ((incidence u v diff).2 h),ite_eq_left h]
      · rw [ite_eq_right (fun t => h ((incidence u v diff).1 t)),ite_eq_right h]

  have petClamp2371 :
      let cap (g : Gate) : Gate := ⟨g.op,g.inputs.map (fun i => min i 28)⟩
      let rd (g : Gate) := if g.op.eval [false,false] then g.inputs.take 1 else g.inputs
      (∀ (gs : List Gate) (u : List Bool) (o : ℕ), u.length + gs.length ≤ 28 →
        (⟨gs.map cap,o⟩ : Circuit).eval u = (⟨gs,o⟩ : Circuit).eval u) ∧
      (∀ (g : Gate) (i : ℕ), i < 28 → (rd (cap g)).contains i = (rd g).contains i) ∧
      (∀ (g : Gate) (i : ℕ), i ∈ (cap g).inputs → i ≤ 28) ∧
      (∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ → FanInTwo ⟨gs.map cap,o⟩) := by
    clear lower9 lowerA lowerB residual petExtend pet2371Seed pet2371Graph pet2371Deck
    intro cap rd
    let step (u : List Bool) (g : Gate) :=
      u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
    have readCap (u : List Bool) (h : u.length ≤ 28) (i : ℕ) :
        u.getD (min i 28) false = u.getD i false := by
      by_cases hi : i ≤ 28
      · rw [Nat.min_eq_left hi]
      · have le : 28 ≤ i := by omega
        rw [Nat.min_eq_right le,List.getD_eq_default _ _ h,List.getD_eq_default _ _ (by omega)]
    have allWire (gs : List Gate) (u : List Bool) (h : u.length + gs.length ≤ 28) :
        (gs.map cap).foldl step u = gs.foldl step u := by
      induction gs generalizing u with
      | nil => rfl
      | cons g gs ih =>
        have bound : u.length ≤ 28 := by simp only [List.length_cons] at h; omega
        have args : g.inputs.map (fun i => u.getD (min i 28) false) = g.inputs.map (fun i => u.getD i false) :=
          List.map_congr_left (fun i _ => readCap u bound i)
        have single : step u (cap g) = step u g := by
          change u ++ [g.op.eval ((g.inputs.map (fun i => min i 28)).map fun i => u.getD i false)] = u ++ [_]
          simp only [List.map_map,Function.comp_def,args]
        simp only [List.map_cons,List.foldl_cons,single]
        apply ih
        simp only [step,List.length_append,List.length_cons,List.length_nil] at h ⊢
        omega
    have used (g : Gate) : rd (cap g) = (rd g).map (fun i => min i 28) := by
      rcases g with ⟨op,ls⟩
      cases c : op.eval [false,false] <;> cases ls <;> simp [cap,rd,c]
    have contains (ls : List ℕ) (j : ℕ) (hj : j < 28) :
        (ls.map (fun i => min i 28)).contains j = ls.contains j := by
      have same (i : ℕ) : (min i 28 == j) = (i == j) ∧ (j == min i 28) = (j == i) := by
        by_cases h : i ≤ 28
        · simp [Nat.min_eq_left h]
        · have le : 28 ≤ i := by omega
          have a : 28 ≠ j := by omega
          have b : i ≠ j := by omega
          simp [Nat.min_eq_right le,a,b,Ne.symm a,Ne.symm b]
      induction ls with
      | nil => rfl
      | cons i ls ih =>
        simp only [List.map_cons,List.contains_cons,(same i).1,(same i).2,ih]
    refine ⟨?_,?_,?_,?_⟩
    · intro gs u o h
      exact congrArg (fun w : List Bool => w.getD o false) (allWire gs u h)
    · intro g i h
      rw [used]
      exact contains (rd g) i h
    · intro g i h
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
      exact Nat.min_le_right _ _
    · intro gs o h g hg
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
      have ok := h k hk
      exact ⟨ok.1,by simpa only [cap,List.length_map] using ok.2⟩

  have pet2371OneNot {n : ℕ} (C : Circuit) (hf : FanInTwo C)
      (count : C.gates.countP (fun g => g.op.eval [false,false]) ≤ 1)
      (f : (Fin n → Bool) → Bool) (lo : f (fun _ => false) = false)
      (hi : f (fun _ => true) = true)
      (hout : ∀ x, (!(C.eval (List.ofFn x))) = f x) :
      ∃ D : Circuit, FanInTwo D ∧ D.size < C.size ∧ ∀ x, D.eval (List.ofFn x) = f x := by
    clear lower9 lowerA lowerB residual petExtend pet2371Seed pet2371Graph pet2371Deck petClamp2371
    classical
    let mark (g : Gate) := g.op.eval [false,false]
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let rel (u v : List Bool) := ∀ i : ℕ, u.getD i false = true → v.getD i false = true
    let leX (x y : Fin n → Bool) := ∀ i : Fin n, x i = true → y i = true
    let bot := fun _ : Fin n => false
    let top := fun _ : Fin n => true
    have botLe (x : Fin n → Bool) : leX bot x := fun _ e => Bool.noConfusion e
    have topLe (x : Fin n → Bool) : leX x top := fun _ _ => rfl
    have rawLe (x y : Fin n → Bool) (xy : leX x y) : rel (List.ofFn x) (List.ofFn y) := by
      intro i
      by_cases h : i < n
      · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h),
          List.getElem_ofFn,List.getElem_ofFn]
        exact xy _
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
        exact id
    have snoc (w : List Bool) (a : Bool) (i : ℕ) :
        (w ++ [a]).getD i false = if i = w.length then a else w.getD i false := by
      induction w generalizing i with
      | nil => cases i <;> rfl
      | cons t ts ih => cases i with
                        | zero => rfl
                        | succ i => simpa using ih i
    have snocLe (u v : List Bool) (a b : Bool) (len : u.length = v.length)
        (uv : rel u v) (ab : a=true → b=true) : rel (u++[a]) (v++[b]) := by
      intro i
      rw [snoc,snoc,len]
      by_cases h : i=v.length
      · simpa only [ite_eq_left h] using ab
      · simpa only [ite_eq_right h] using uv i
    have run (gs : List Gate) (kind : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
        (u v : List Bool) (len : u.length=v.length) (uv : rel u v) :
        rel (gs.foldl step u) (gs.foldl step v) := by
      induction gs generalizing u v with
      | nil => exact uv
      | cons g gs ih =>
        have next : g.op.eval (g.inputs.map fun i => u.getD i false) = true →
            g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
          rcases kind _ (List.mem_cons_self) with op | op
          · rw [op]
            change (g.inputs.map _).all id = true → (g.inputs.map _).all id = true
            simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
            exact fun acc i hm => uv i (acc i hm)
          · rw [op]
            change (g.inputs.map _).any id = true → (g.inputs.map _).any id = true
            simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
            rintro ⟨i,hm,one⟩
            exact ⟨i,hm,uv _ one⟩
        rw [List.foldl_cons,List.foldl_cons]
        exact ih (fun h hh => kind h (List.mem_cons_of_mem _ hh)) _ _
          (by simp [step,len]) (snocLe _ _ _ _ len uv next)
    have flip (u v : Bool) (h : (!u) = v) : u = !v := by
      cases u <;> cases v <;> first | rfl | exact Bool.noConfusion h
    have atBot : C.eval (List.ofFn bot) = true := (flip _ _ (hout bot)).trans (congrArg Bool.not lo)
    have atTop : C.eval (List.ofFn top) = false := (flip _ _ (hout top)).trans (congrArg Bool.not hi)
    have splitMember (gs : List Gate) (g : Gate) (mem : g ∈ gs) :
        ∃ pre tail, gs = pre ++ g :: tail := by
      induction gs with
      | nil => cases mem
      | cons a gs ih =>
        rcases List.mem_cons.mp mem with e | e
        · exact ⟨[],gs,by rw [e]; rfl⟩
        · obtain ⟨p,s,eq⟩ := ih e
          exact ⟨a::p,s,by rw [eq]; rfl⟩
    have unmarked (gs : List Gate) (hz : gs.countP mark = 0) : ∀ g ∈ gs, mark g = false := by
      induction gs with
      | nil => intro g h; cases h
      | cons g gs ih =>
        cases e : mark g with
        | false =>
          have z : gs.countP mark = 0 := by simpa [List.countP_cons,e] using hz
          intro a ha
          rcases List.mem_cons.mp ha with h | h
          · exact h ▸ e
          · exact ih z a h
        | true => simp [List.countP_cons,e] at hz
    have monoOf (g : Gate) (hg : g ∈ C.gates) (no : g.op ≠ .not) : g.op=.and ∨ g.op=.or := by
      have h := (hf g hg).1
      change g.op=.and ∨ g.op=.or ∨ g.op=.not at h
      rcases h with e | e | e
      · exact Or.inl e
      · exact Or.inr e
      · exact (no e).elim
    by_cases occurs : ∃ g ∈ C.gates, g.op=.not
    · obtain ⟨g,mem,hnot⟩ := occurs
      obtain ⟨p,s,hgs⟩ := splitMember C.gates g mem
      have m : mark g = true := by change g.op.eval [false,false] = true; rw [hnot]; rfl
      have num : p.countP mark + s.countP mark + 1 ≤ 1 := by
        change C.gates.countP mark ≤ 1 at count
        rw [hgs,List.countP_append,List.countP_cons] at count
        simpa [m,Nat.add_assoc] using count
      have noP := unmarked p (by omega)
      have noS := unmarked s (by omega)
      have preG (h : Gate) (mem : h ∈ p) : h ∈ C.gates := by rw [hgs]; exact List.mem_append_left _ mem
      have endG (h : Gate) (mem : h ∈ s) : h ∈ C.gates := by
        rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ mem)
      have kP : ∀ h ∈ p, h.op=.and ∨ h.op=.or := by
        intro h mem
        apply monoOf h (preG h mem)
        intro hn
        have bad := noP h mem
        change h.op.eval [false,false] = false at bad
        rw [hn] at bad
        exact Bool.noConfusion bad
      have kS : ∀ h ∈ s, h.op=.and ∨ h.op=.or := by
        intro h mem
        apply monoOf h (endG h mem)
        intro hn
        have bad := noS h mem
        change h.op.eval [false,false] = false at bad
        rw [hn] at bad
        exact Bool.noConfusion bad
      let pre (x : Fin n → Bool) := p.foldl step (List.ofFn x)
      let j := g.inputs.headD (n+p.length)
      let q (x : Fin n → Bool) := (pre x).getD j false
      have sizeW (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length+gs.length := by
        induction gs generalizing w with
        | nil => simp
        | cons h gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
      have lengthP (x : Fin n → Bool) : (pre x).length = n+p.length := by
        dsimp only [pre]
        rw [sizeW,List.length_ofFn]
      have inverted (x : Fin n → Bool) : g.op.eval (g.inputs.map fun i => (pre x).getD i false) = !q x := by
        dsimp only [q,j]
        rw [hnot]
        cases e : g.inputs with
        | nil => change true = !((pre x).getD (n+p.length) false); rw [List.getD_eq_default _ _ (by rw [lengthP])]; rfl
        | cons a l => rfl
      have whole (x : Fin n → Bool) : C.eval (List.ofFn x) = (s.foldl step (pre x ++ [!q x])).getD C.output false := by
        change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
        rw [hgs,List.foldl_append,List.foldl_cons]
        change (s.foldl step ((pre x) ++ [g.op.eval (g.inputs.map fun i => (pre x).getD i false)])).getD C.output false = _
        rw [inverted]
      have preLe (x y : Fin n → Bool) (h : leX x y) : rel (pre x) (pre y) :=
        run p kP _ _ (by simp) (rawLe _ _ h)
      have stable (x y : Fin n → Bool) (h : leX x y) (same : q x = q y) :
          C.eval (List.ofFn x)=true → C.eval (List.ofFn y)=true := by
        rw [whole,whole]
        apply run s kS _ _ (by simp only [List.length_append,List.length_singleton,lengthP]) _ C.output
        apply snocLe _ _ _ _ (by rw [lengthP,lengthP]) (preLe _ _ h)
        rw [same]
        exact id
      refine ⟨⟨p,j⟩,(fun h mem => hf h (preG h mem)),?_,?_⟩
      · change p.length < C.gates.length
        rw [hgs,List.length_append,List.length_cons]
        omega
      · intro x
        change q x = f x
        cases e : q x with
        | false =>
          have b : q bot = false := by
            cases k : q bot with
            | false => rfl
            | true => exact Bool.noConfusion ((preLe _ _ (botLe x) j k).symm.trans e)
          have cx := stable bot x (botLe x) (b.trans e.symm) atBot
          exact (congrArg Bool.not cx).symm.trans (hout x)
        | true =>
          have t : q top = true := preLe _ _ (topLe x) j e
          have cx : C.eval (List.ofFn x) = false := by
            apply Bool.eq_false_iff.mpr
            intro pos
            exact Bool.noConfusion ((stable x top (topLe x) (e.trans t.symm) pos).symm.trans atTop)
          exact (congrArg Bool.not cx).symm.trans (hout x)
    · have all : ∀ g ∈ C.gates, g.op=.and ∨ g.op=.or :=
        fun g mem => monoOf g mem (fun op => occurs ⟨g,mem,op⟩)
      have risen : C.eval (List.ofFn top) = true := run _ all _ _ (by simp) (rawLe _ _ (botLe top)) C.output atBot
      exact (Bool.noConfusion (risen.symm.trans atTop))

  classical
  let F := (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
    (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) ||
    (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
  let E (i j : Fin 10) :=
    (([[1, 4, 5], [2, 6], [3, 7], [4, 8], [9],
       [7, 8], [8, 9], [9], [], []] : List (List ℕ)).getD
      (min i.val j.val) []).contains (max i.val j.val)
  let nine := (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun d => x (Fin.ofNat 9 (d / 10)) && x (Fin.ofNat 9 (d % 10))))
  let adjacent := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) ||
      (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
  let separate := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 5 && x 7))
  let R (u v a d : Fin 10) (s t : Bool) (x : Fin 10 → Bool) (i : Fin 10) :=
    if i = u ∨ i = v then (if i = u then s else t) && (x a && x d) else x i
  let score (D : Circuit) (r : (Fin 10 → Bool) → Fin 10 → Bool) :=
    let w (j : ℕ) (x : Fin 10 → Bool) := (D.wires (List.ofFn (r x))).getD j false
    ((Finset.range (10+D.size)).image w \ insert (fun _ => false) ((Finset.range 10).image w)).card
  have project {α β : Type} [DecidableEq α] [DecidableEq β] (h : α → β) (A B : Finset α) :
      (A.image h \ B.image h).card ≤ (A \ B).card := by
    apply Nat.le_trans (m := ((A \ B).image h).card) _ Finset.card_image_le
    apply Finset.card_le_card
    intro y hy
    obtain ⟨hA,hB⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA
    exact Finset.mem_image.mpr ⟨x,Finset.mem_sdiff.mpr ⟨hx,fun q => hB (Finset.mem_image_of_mem h q)⟩,rfl⟩
  have witnesses (x : Fin 10 → Bool) :
      F x = decide (∃ i j, E i j = true ∧ x i = true ∧ x j = true) := pet2371Graph.1 x
  have profiles (D : Circuit) (fan : FanInTwo D) (right : ∀ x, D.eval (List.ofFn x) = F x) :
      ∀ (u v a d : Fin 10) (s t : Bool), E a d = true →
      (if u=v then 15 else if E u v then 13 else 12) ≤
      (if s || t then 1 else 0) + score D (R u v a d s t) := by
    intro u v a d s t edge
    let r := R u v a d s t
    let W (j : ℕ) (x : Fin 10 → Bool) := (D.wires (List.ofFn (r x))).getD j false
    have test (n L : ℕ) (target : (Fin n → Bool) → Bool) (lower : ¬ HasCircuitSize n target L)
        (lift : (Fin n → Bool) → Fin 10 → Bool)
        (pin : ∀ x, lift x u = false ∧ lift x v = false)
        (axes : ∀ j, (∀ x, lift x j = false) ∨ ∃ i : Fin n, ∀ x, lift x j = x i)
        (matchF : ∀ x, F (lift x) = target x) :
        L + 1 ≤ (if s || t then 1 else 0) + score D r := by
      have allowed (x : Fin n → Bool) : F (r (lift x)) = F (lift x) := by
        have absent (i : Fin 10) (h : i = u ∨ i = v) : lift x i = false := by
          rcases h with hu | hv
          · simpa only [hu] using (pin x).1
          · simpa only [hv] using (pin x).2
        by_cases hot : (lift x a && lift x d) = true
        · have ad := Bool.and_eq_true_iff.mp hot
          have keep (i : Fin 10) (hi : lift x i = true) : r (lift x) i = true := by
            have outside : ¬ (i=u ∨ i=v) := fun h => Bool.noConfusion ((absent i h).symm.trans hi)
            simpa only [r,R,ite_eq_right outside] using hi
          have hit (y : Fin 10 → Bool) (ha : y a = true) (hd : y d = true) : F y = true := by
            rw [witnesses]
            exact decide_eq_true ⟨a,d,edge,ha,hd⟩
          exact (hit _ (keep a ad.1) (keep d ad.2)).trans (hit _ ad.1 ad.2).symm
        · have off := Bool.eq_false_iff.mpr hot
          have same : r (lift x) = lift x := by
            funext i
            by_cases h : i=u ∨ i=v
            · simp only [r,R,ite_eq_left h,off,Bool.and_false,absent i h]
            · simp only [r,R,ite_eq_right h]
          rw [same]
      obtain ⟨base,baseFan,price,init⟩ := pet2371Seed n lift axes u v a d s t
      let seed (x : Fin n → Bool) := List.ofFn (r (lift x))
      let w (j : ℕ) (x : Fin n → Bool) := W j (lift x)
      let pull (f : (Fin 10 → Bool) → Bool) (x : Fin n → Bool) := f (lift x)
      let k := ((Finset.range (10+D.size)).image w \ insert (fun _ => false) ((Finset.range 10).image w)).card
      have h0 := petExtend n 10 D.gates seed (by simp [seed]) base baseFan init fan D.output
      have reach : HasCircuitSize n (fun x => D.eval (seed x)) (base.size+k) := by
        convert h0 using 1 <;> first | rfl | (congr 1; ext f; simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_image]; rfl)
      have limit : L+1 ≤ base.size+k := by
        by_contra! few
        obtain ⟨Z,hz,sz,evalZ⟩ := reach
        exact lower ⟨Z,hz,sz.trans (by omega),fun x =>
          (evalZ x).trans ((right _).trans ((allowed x).trans (matchF x)))⟩
      have images (j : ℕ) : ((Finset.range j).image W).image pull = (Finset.range j).image w := by
        rw [Finset.image_image]
        rfl
      have smaller : k ≤ score D r := by
        have h := project pull ((Finset.range (10+D.size)).image W)
          (insert (fun _ => false) ((Finset.range 10).image W))
        simpa only [Finset.image_insert,images] using h
      exact limit.trans (Nat.add_le_add price smaller)
    by_cases eq : u = v
    · subst v
      obtain ⟨lift,h,axis,ag⟩ := pet2371Deck.1 u
      simpa only [ite_eq_left rfl,ite_true] using (test 9 14 nine lower9 lift (fun x => ⟨h x,h x⟩) axis ag)
    · obtain ⟨lift,pin,axis,ag⟩ := pet2371Deck.2 u v eq
      change ∀ x, F (lift x) = (if F (fun i => decide (i=u ∨ i=v)) then adjacent x else separate x) at ag
      have tab : E u v = F (fun i => decide (i = u ∨ i = v)) := pet2371Graph.2 u v
      by_cases e : E u v = true
      · have matchF (x) : F (lift x) = adjacent x := by
          have h : F (fun i => decide (i=u ∨ i=v)) = true := tab.symm.trans e
          simpa only [h,ite_true] using ag x
        simpa only [ite_eq_right eq,ite_eq_left e] using (test 8 12 adjacent lowerA lift pin axis matchF)
      · have matchF (x) : F (lift x) = separate x := by
          have h : ¬ F (fun i => decide (i=u ∨ i=v)) = true := fun h => e (tab.trans h)
          simpa only [ite_eq_right h] using ag x
        simpa only [ite_eq_right eq,ite_eq_right e] using (test 8 11 separate lowerB lift pin axis matchF)
  intro g tail out sign fg ft small posted tapped
  by_contra none
  let A : Circuit := ⟨g :: tail.gates,out⟩
  have initialFan : FanInTwo A := by
    intro h hh
    rcases List.mem_cons.mp hh with e | e
    · exact fg h (List.mem_singleton.mpr e)
    · exact ft h e
  have initialSize : A.size ≤ 18 := by
    change tail.gates.length + 1 ≤ 18
    change tail.gates.length ≤ 17 at small
    omega
  have initial (x : Fin 10 → Bool) :
      (if sign then !(A.eval (List.ofFn x)) else A.eval (List.ofFn x)) = F x := by
    by_contra e
    exact none ⟨x,e⟩
  -- Minimize across both polarities so a shorter positive realization also wins.
  let can (k : ℕ) := ∃ (Q : Circuit) (b : Bool), FanInTwo Q ∧ Q.size = k ∧
    ∀ x : Fin 10 → Bool, (if b then !(Q.eval (List.ofFn x)) else Q.eval (List.ofFn x)) = F x
  have orig : can A.size := ⟨A,sign,initialFan,rfl,initial⟩
  have someSize : ∃ k, can k := ⟨_,orig⟩
  obtain ⟨Q,b,qFan,qSize,qGood⟩ := Nat.find_spec someSize
  have least (Z : Circuit) (c : Bool) (zf : FanInTwo Z)
      (ok : ∀ x : Fin 10 → Bool, (if c then !(Z.eval (List.ofFn x)) else Z.eval (List.ofFn x)) = F x) :
      Q.size ≤ Z.size := by
    rw [qSize]
    exact Nat.find_min' someSize (show can Z.size from ⟨Z,c,zf,rfl,ok⟩)
  have bound := (least A sign initialFan initial).trans initialSize
  let step (w : List Bool) (h : Gate) := w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
  have lens (ls : List Gate) (w : List Bool) : (ls.foldl step w).length = w.length + ls.length := by
    induction ls generalizing w with
    | nil => simp
    | cons g ls ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have snoc (ls : List Bool) (v : Bool) (i : ℕ) (ne : i ≠ ls.length) :
      (ls++[v]).getD i false = ls.getD i false := by
    by_cases h : i < ls.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
  have noRaw : ∀ (j : Fin 11) (c : Bool), ∃ x : Fin 10 → Bool,
      (if c then !((List.ofFn x).getD j.val false) else (List.ofFn x).getD j.val false) ≠ F x := by
    have samples : ∀ (j : Fin 11) (c : Bool), ∃ p : Fin 12,
        let x := fun i : Fin 10 => if p.val < 10 then decide (i.val = p.val) else decide (p.val = 10)
        (if c then !((List.ofFn x).getD j.val false) else (List.ofFn x).getD j.val false) ≠ F x := by decide +kernel
    intro j c
    obtain ⟨p,h⟩ := samples j c
    exact ⟨_,h⟩
  have finalWire (ls : List Gate) (shape : Q.gates = ls) : Q.output = 9+ls.length := by
    induction ls using List.reverseRecOn with
    | nil =>
      exfalso
      let j : Fin 11 := ⟨min Q.output 10,by omega⟩
      obtain ⟨x,err⟩ := noRaw j b
      have rawOut : Q.eval (List.ofFn x) = (List.ofFn x).getD j.val false := by
        change (Q.gates.foldl step (List.ofFn x)).getD Q.output false = _
        rw [shape,List.foldl_nil]
        by_cases le : Q.output ≤ 10
        · simp [j,Nat.min_eq_left le]
        · have gte : 10 ≤ Q.output := by omega
          simp only [j,Nat.min_eq_right gte]
          rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp)]
      apply err
      rw [← rawOut]
      exact qGood x
    | append_singleton p last _ =>
      by_contra e
      let Z : Circuit := ⟨p,Q.output⟩
      have okZ : FanInTwo Z := by
        intro h hh
        apply qFan h
        rw [shape]
        exact List.mem_append_left _ hh
      have same (x : Fin 10 → Bool) : Q.eval (List.ofFn x) = Z.eval (List.ofFn x) := by
        change (Q.gates.foldl step (List.ofFn x)).getD Q.output false = _
        rw [shape,List.foldl_append]
        change (p.foldl step (List.ofFn x) ++ [_]).getD Q.output false = _
        apply snoc
        rw [lens,List.length_ofFn]
        simp only [List.length_append,List.length_singleton] at e
        omega
      have le := least Z b okZ (fun x => by rw [← same]; exact qGood x)
      change Q.gates.length ≤ p.length at le
      rw [shape,List.length_append,List.length_singleton] at le
      omega
  have atEnd := finalWire Q.gates rfl
  let cap (h : Gate) : Gate := ⟨h.op,h.inputs.map fun i => min i 28⟩
  let C : Circuit := ⟨Q.gates.map cap,Q.output⟩
  have cfan : FanInTwo C := petClamp2371.2.2.2 Q.gates Q.output qFan
  have sz : C.size = Q.size := List.length_map cap
  have signed (x : Fin 10 → Bool) :
      (if b then !(C.eval (List.ofFn x)) else C.eval (List.ofFn x)) = F x := by
    have h := petClamp2371.1 Q.gates (List.ofFn x) Q.output (by simp; change Q.gates.length ≤ 18 at bound; omega)
    change C.eval (List.ofFn x) = Q.eval (List.ofFn x) at h
    rw [h]
    exact qGood x
  have bounded : ∀ i ∈ C.gates.flatMap Gate.inputs, i ≤ 28 := by
    intro i hi
    obtain ⟨h,hh,inside⟩ := List.mem_flatMap.mp hi
    obtain ⟨g,_,rfl⟩ := List.mem_map.mp hh
    exact petClamp2371.2.2.1 g i inside
  -- Compression with an empty seed recovers every reusable wire of the full circuit.
  have width : C.size ≤ score C id := by
    let empty : Circuit := ⟨[],0⟩
    have fe : FanInTwo empty := by intro h hh; cases hh
    have init (i : ℕ) : ∃ k, ∀ x : Fin 10 → Bool,
        (empty.wires (List.ofFn x)).getD k false = (List.ofFn x).getD i false := ⟨i,fun x => rfl⟩
    have h := petExtend 10 10 C.gates (fun x => List.ofFn x) (by simp) empty fe init cfan C.output
    have reach : HasCircuitSize 10 (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) (score C id) := by
      simp only [show empty.size = 0 by rfl, Nat.zero_add] at h
      convert h using 1 <;> first | rfl | (congr 1; ext f; simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_image]; rfl)
    obtain ⟨Z,fz,smallZ,eZ⟩ := reach
    rw [sz]
    exact (least Z b fz (fun x => by rw [eZ]; exact signed x)).trans smallZ
  -- With these endpoint values, one inversion gives a shorter positive circuit.
  have ncount : b = true → 2 ≤ C.gates.countP (fun h => h.op.eval [false,false]) := by
    intro hb
    by_contra! few
    obtain ⟨Z,fz,lt,ok⟩ := pet2371OneNot C cfan (by omega) F rfl rfl (fun x => by simpa only [hb,ite_true] using signed x)
    have up := least Z false fz ok
    omega
  -- The extra gate names the target at either polarity before scoring restrictions.
  let finish : Gate := ⟨if b then .not else .or,[C.output]⟩
  let D : Circuit := ⟨C.gates++[finish],10+C.size⟩
  have dFan : FanInTwo D := by
    intro h hh
    rcases List.mem_append.mp hh with real | endGate
    · exact cfan h real
    · obtain rfl := List.mem_singleton.mp endGate
      refine ⟨?_,by change 1 ≤ 2; decide⟩
      cases b
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have dgood (x : Fin 10 → Bool) : D.eval (List.ofFn x) = F x := by
    let w := C.wires (List.ofFn x)
    have len : w.length = 10+C.size := by
      change (C.gates.foldl step (List.ofFn x)).length = _
      rw [lens,List.length_ofFn]
      rfl
    have truth (v : Bool) : (if b then GateOp.not else GateOp.or).eval [v] = if b then !v else v := by
      cases b <;> cases v <;> rfl
    change ((C.gates++[finish]).foldl step (List.ofFn x)).getD (10+C.size) false = _
    rw [List.foldl_append]
    change (w++[(if b then GateOp.not else GateOp.or).eval [w.getD C.output false]]).getD (10+C.size) false = _
    rw [←len,show ∀ v : Bool, (w++[v]).getD w.length false = v by simp,truth]
    exact signed x
  have lastC : C.output = 9+C.size := by rw [sz]; exact atEnd
  apply residual C b cfan (sz.le.trans bound) lastC bounded width ncount (profiles D dFan dgood)
  intro x
  exact (dgood x).trans (witnesses x)
