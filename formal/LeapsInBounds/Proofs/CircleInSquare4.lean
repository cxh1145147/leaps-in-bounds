module

public import LeapsInBounds.Statements.CircleInSquare

/-!
# Lower bound for packing 4 unit circles in a square

Proves `s(4) ≥ 4` (`RadicalLowerBound 4 [(4, 1)] 1`): if 4 closed unit disks fit
in `[0, s]²` with `s < 4`, shifting their centers by `(-2, -2)` places them in
`[-1, 1]²` with pairwise squared distances at least `4`. Partitioning `[-1, 1]²`
into four quadrants places one center in each quadrant, and summing the four
cyclic neighbor squared distances via a nonnegative polynomial identity forces
`4 ≤ s`.
-/

public section

namespace LeapsInBounds.Proofs.CircleInSquare4

open CircleInSquare

private lemma add_mem_closedBall (p : Plane) {u v : ℝ} (h : u ^ 2 + v ^ 2 ≤ 1) :
    p + !₂[u, v] ∈ Metric.closedBall p 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, EuclideanSpace.norm_eq]
  simpa [Fin.sum_univ_two] using h

private lemma center_bounds {s : ℝ} {p : Plane} (h : Metric.closedBall p 1 ⊆ square s) :
    1 ≤ p 0 ∧ p 0 ≤ s - 1 ∧ 1 ≤ p 1 ∧ p 1 ≤ s - 1 := by
  have h1 := h (add_mem_closedBall p (u := -1) (v := 0) (by norm_num))
  have h2 := h (add_mem_closedBall p (u := 1) (v := 0) (by norm_num))
  have h3 := h (add_mem_closedBall p (u := 0) (v := -1) (by norm_num))
  have h4 := h (add_mem_closedBall p (u := 0) (v := 1) (by norm_num))
  simp only [square, Set.mem_ofPred_eq, PiLp.add_apply] at h1 h2 h3 h4
  simp at h1 h2 h3 h4
  refine ⟨by linarith [h1.1], by linarith [h2.2.1], by linarith [h3.2.2.1], by linarith [h4.2.2.2]⟩

private lemma four_le_dist_sq {n : ℕ} {s : ℝ} {c : Fin n → Plane} (h : IsPacking s c)
    {i j : Fin n} (hij : i ≠ j) :
    4 ≤ (c i 0 - c j 0) ^ 2 + (c i 1 - c j 1) ^ 2 := by
  have h2 := (disjoint_ball_ball_iff one_pos one_pos).1 (h.2.2 i j hij)
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs] at h2
  nlinarith [Real.sq_sqrt (show 0 ≤ (c i 0 - c j 0) ^ 2 + (c i 1 - c j 1) ^ 2 by positivity)]

-- Work in [-1, 1]², assigning both coordinate axes to the nonpositive side.
private noncomputable def side (x : ℝ) : Bool :=
  by classical exact decide (0 < x)

private lemma half_bounds {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) (b : Bool) (hb : side x = b) :
    0 ≤ (if b then x else -x) ∧ (if b then x else -x) ≤ 1 := by
  classical
  cases b <;> simp_all [side] <;> linarith

private lemma same_half {x y : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1)
    (h : side x = side y) : (x - y) ^ 2 ≤ 1 := by
  have bx := half_bounds hx (side y) h
  have by' := half_bounds hy (side y) rfl
  cases hs : side y <;> simp [hs] at bx by' <;>
    nlinarith only [mul_nonneg (show 0 ≤ 1 - (x - y) by linarith)
                              (show 0 ≤ 1 + (x - y) by linarith)]

private def edges (a b c d : ℝ) : ℝ :=
  (a + b) ^ 2 + (b - c) ^ 2 + (c + d) ^ 2 + (d - a) ^ 2

private lemma edge_bound {a b c d : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1) :
    edges a b c d + (1 - a) + (1 - b) + (1 - c) + (1 - d) ≤ 8 := by
  unfold edges
  nlinarith only [sq_nonneg ((a - c) - (b - d)),
    mul_nonneg (sub_nonneg.mpr ha.2) ha.1, mul_nonneg (sub_nonneg.mpr hb.2) hb.1,
    mul_nonneg (sub_nonneg.mpr hc.2) hc.1, mul_nonneg (sub_nonneg.mpr hd.2) hd.1,
    mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hc.2),
    mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr hd.2)]

/-- `s(4) ≥ 4`. -/
theorem lower_four : RadicalLowerBound 4 [(4, 1)] 1 := by
  norm_num [RadicalLowerBound, radical]
  intro s c hc
  by_contra! hs
  let x (i : Fin 4) : ℝ := c i 0 - 2
  let y (i : Fin 4) : ℝ := c i 1 - 2
  have raw_bounds (i : Fin 4) :
      (-1 ≤ x i ∧ x i ≤ s - 3) ∧ (-1 ≤ y i ∧ y i ≤ s - 3) := by
    obtain ⟨hx, hx', hy, hy'⟩ := center_bounds (hc.2.1 i)
    exact ⟨⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩,
           ⟨by dsimp [y]; linarith, by dsimp [y]; linarith⟩⟩
  have bounds (i : Fin 4) : (-1 ≤ x i ∧ x i ≤ 1) ∧ (-1 ≤ y i ∧ y i ≤ 1) :=
    ⟨⟨(raw_bounds i).1.1, by linarith [(raw_bounds i).1.2]⟩,
     ⟨(raw_bounds i).2.1, by linarith [(raw_bounds i).2.2]⟩⟩
  have sep (i j : Fin 4) (hij : i ≠ j) : 4 ≤ (x i - x j) ^ 2 + (y i - y j) ^ 2 := by
    have h' := four_le_dist_sq hc hij
    dsimp [x, y]
    linarith only [h']
  let quad (i : Fin 4) : Bool × Bool := (side (x i), side (y i))
  have injective : Function.Injective quad := by
    intro i j h
    by_contra hij
    have dx := same_half (bounds i).1 (bounds j).1 (congrArg Prod.fst h)
    have dy := same_half (bounds i).2 (bounds j).2 (congrArg Prod.snd h)
    linarith only [dx, dy, sep i j hij]
  let e : (Bool × Bool) ≃ Fin 4 :=
    (Equiv.ofBijective quad
      ((Fintype.bijective_iff_injective_and_card quad).2 ⟨injective, by decide⟩)).symm
  have sides (a b : Bool) : quad (e (a, b)) = (a, b) := e.symm_apply_apply _
  let X (a b : Bool) : ℝ := x (e (a, b))
  let Y (a b : Bool) : ℝ := y (e (a, b))
  have bx (a b : Bool) : 0 ≤ (if a then X a b else -X a b) ∧
      (if a then X a b else -X a b) ≤ 1 :=
    half_bounds (bounds (e (a, b))).1 a (congrArg Prod.fst (sides a b))
  have by' (a b : Bool) : 0 ≤ (if b then Y a b else -Y a b) ∧
      (if b then Y a b else -Y a b) ≤ 1 :=
    half_bounds (bounds (e (a, b))).2 b (congrArg Prod.snd (sides a b))
  have ex := edge_bound (bx false false) (bx true false) (bx true true) (bx false true)
  have ey := edge_bound (by' true false) (by' true true) (by' false true) (by' false false)
  have neighbor (a b u v : Bool) (h : (a, b) ≠ (u, v)) :
      4 ≤ (X a b - X u v) ^ 2 + (Y a b - Y u v) ^ 2 := sep _ _ (e.injective.ne h)
  have perimeter := add_le_add
    (add_le_add (neighbor false false true false (by decide))
      (neighbor true false true true (by decide)))
    (add_le_add (neighbor true true false true (by decide))
      (neighbor false true false false (by decide)))
  have total : 8 ≤ -X false false + X true false + X true true - X false true
      - Y true false + Y true true + Y false true - Y false false := by
    simp only [Bool.false_eq_true, ↓reduceIte, edges] at ex ey
    linarith only [ex, ey, perimeter]
  have r00 := raw_bounds (e (false, false))
  have r10 := raw_bounds (e (true, false))
  have r11 := raw_bounds (e (true, true))
  have r01 := raw_bounds (e (false, true))
  dsimp [X, Y] at total
  linarith [r00.1.1, r00.2.1, r10.1.2, r10.2.1, r11.1.2, r11.2.2, r01.1.1, r01.2.2]

end LeapsInBounds.Proofs.CircleInSquare4
