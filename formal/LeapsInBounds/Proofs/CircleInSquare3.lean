module

public import LeapsInBounds.Statements.CircleInSquare

/-!
# Lower bound for packing 3 unit circles in a square

Proves `s(3) ≥ 2 + √2 / 2 + √6 / 2` (`RadicalLowerBound 3 [(4, 1), (1, 2), (1, 6)] 2`).
Shifting the centers by `(-1, -1)` places them in `[0, s - 2]²` with pairwise
squared distances at least `4`. Sorting by the `x`-coordinate reduces monotone
`y`-orders to `s - 2 ≥ 2` and non-monotone `y`-orders (up to axis reflections)
to a single configuration whose three separation bounds imply
`(s - 2)² ≥ 2 + √3`, i.e. `s ≥ 2 + (√2 + √6) / 2`.
-/

public section

namespace LeapsInBounds.Proofs.CircleInSquare3

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

private lemma sqrt_two_add_sqrt_six_sq :
    (Real.sqrt 2 + Real.sqrt 6) ^ 2 = 4 * (2 + Real.sqrt 3) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h2n : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h3n : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h6n : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hprod : Real.sqrt 2 * Real.sqrt 6 = 2 * Real.sqrt 3 := by
    have hsq : (Real.sqrt 2 * Real.sqrt 6) ^ 2 = (2 * Real.sqrt 3) ^ 2 := by
      calc
        (Real.sqrt 2 * Real.sqrt 6) ^ 2 = Real.sqrt 2 ^ 2 * Real.sqrt 6 ^ 2 := by ring
        _ = 12 := by rw [h2, h6]; norm_num
        _ = (2 * Real.sqrt 3) ^ 2 := by rw [mul_pow, h3]; norm_num
    have hdiff : (Real.sqrt 2 * Real.sqrt 6 - 2 * Real.sqrt 3) *
        (Real.sqrt 2 * Real.sqrt 6 + 2 * Real.sqrt 3) = 0 := by linarith
    rcases mul_eq_zero.mp hdiff with h | h <;> linarith [mul_nonneg h2n h6n]
  nlinarith only [h2, h6, hprod]

private lemma ordered_case {L x0 x1 x2 y0 y1 y2 : ℝ}
    (hx0 : 0 ≤ x0) (hx01 : x0 ≤ x1) (hx12 : x1 ≤ x2) (hx2L : x2 ≤ L)
    (hy1 : 0 ≤ y1) (hy10 : y1 ≤ y0) (hy02 : y0 ≤ y2) (hy2L : y2 ≤ L)
    (h01 : 4 ≤ (x0 - x1) ^ 2 + (y0 - y1) ^ 2)
    (h12 : 4 ≤ (x1 - x2) ^ 2 + (y1 - y2) ^ 2)
    (h02 : 4 ≤ (x0 - x2) ^ 2 + (y0 - y2) ^ 2) :
    (Real.sqrt 2 + Real.sqrt 6) / 2 ≤ L := by
  by_contra! hL
  have hL0 : 0 ≤ L := by linarith
  have h3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3n : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h3lt2 : Real.sqrt 3 < 2 := by nlinarith only [h3sq, h3n]
  have h2n : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h6n : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have hLsq_lt : L ^ 2 < 2 + Real.sqrt 3 := by
    have hsum := sqrt_two_add_sqrt_six_sq
    have hd : 0 < (Real.sqrt 2 + Real.sqrt 6) / 2 - L := by linarith
    have hs : 0 < (Real.sqrt 2 + Real.sqrt 6) / 2 + L := by linarith
    nlinarith only [mul_pos hd hs, hsum]
  have hLsq_lt4 : L ^ 2 < 4 := by linarith
  have h2_le_Lsq : 2 ≤ L ^ 2 := by
    have hx : (x0 - x1) ^ 2 ≤ L ^ 2 := by
      nlinarith only [mul_nonneg (show 0 ≤ L - (x1 - x0) by linarith)
                                 (show 0 ≤ L + (x1 - x0) by linarith)]
    have hy : (y0 - y1) ^ 2 ≤ L ^ 2 := by
      nlinarith only [mul_nonneg (show 0 ≤ L - (y0 - y1) by linarith)
                                 (show 0 ≤ L + (y0 - y1) by linarith)]
    linarith
  set a : ℝ := x1 - x0
  set c : ℝ := y0 - y1
  set w : ℝ := Real.sqrt (4 - L ^ 2)
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hwsq : w ^ 2 = 4 - L ^ 2 := Real.sq_sqrt (by linarith)
  have ha_le : a ≤ L - w := by
    have hx : (x1 - x2) ^ 2 ≤ (L - a) ^ 2 := by
      nlinarith only [mul_nonneg (show 0 ≤ (L - a) - (x2 - x1) by linarith)
                                 (show 0 ≤ (L - a) + (x2 - x1) by linarith)]
    have hy : (y1 - y2) ^ 2 ≤ L ^ 2 := by
      nlinarith only [mul_nonneg (show 0 ≤ L - (y2 - y1) by linarith)
                                 (show 0 ≤ L + (y2 - y1) by linarith)]
    have hwa : w ^ 2 ≤ (L - a) ^ 2 := by linarith
    by_contra! hlt
    have h1 : 0 < w - (L - a) := by linarith
    have h2 : 0 < w + (L - a) := by linarith
    nlinarith only [mul_pos h1 h2, hwa]
  have hc_le : c ≤ L - w := by
    have hx : (x0 - x2) ^ 2 ≤ L ^ 2 := by
      nlinarith only [mul_nonneg (show 0 ≤ L - (x2 - x0) by linarith)
                                 (show 0 ≤ L + (x2 - x0) by linarith)]
    have hy : (y0 - y2) ^ 2 ≤ (L - c) ^ 2 := by
      nlinarith only [mul_nonneg (show 0 ≤ (L - c) - (y2 - y0) by linarith)
                                 (show 0 ≤ (L - c) + (y2 - y0) by linarith)]
    have hwc : w ^ 2 ≤ (L - c) ^ 2 := by linarith
    by_contra! hlt
    have h1 : 0 < w - (L - c) := by linarith
    have h2 : 0 < w + (L - c) := by linarith
    nlinarith only [mul_pos h1 h2, hwc]
  have hLw_le : L * w ≤ 1 := by
    have ha2 : a ^ 2 ≤ (L - w) ^ 2 := by
      nlinarith only [mul_nonneg (show 0 ≤ (L - w) - a by linarith)
                                 (show 0 ≤ (L - w) + a by linarith)]
    have hc2 : c ^ 2 ≤ (L - w) ^ 2 := by
      nlinarith only [mul_nonneg (show 0 ≤ (L - w) - c by linarith)
                                 (show 0 ≤ (L - w) + c by linarith)]
    have h4ac : 4 ≤ a ^ 2 + c ^ 2 := by
      dsimp [a, c]
      nlinarith only [h01]
    nlinarith only [ha2, hc2, h4ac, hwsq]
  have hLw_sq : L ^ 2 * (4 - L ^ 2) ≤ 1 := by
    have hLw0 : 0 ≤ L * w := mul_nonneg hL0 hw0
    have hsq : (L * w) ^ 2 ≤ 1 := by
      nlinarith only [mul_nonneg (show 0 ≤ 1 - L * w by linarith)
                                 (show 0 ≤ 1 + L * w by linarith)]
    calc
      L ^ 2 * (4 - L ^ 2) = L ^ 2 * w ^ 2 := by rw [hwsq]
      _ = (L * w) ^ 2 := by ring
      _ ≤ 1 := hsq
  have h1 : 0 < Real.sqrt 3 - (L ^ 2 - 2) := by linarith
  have h2 : 0 < Real.sqrt 3 + (L ^ 2 - 2) := by linarith
  nlinarith only [mul_pos h1 h2, hLw_sq, h3sq]

private lemma monotone_y_case {L x0 x1 x2 y0 y1 y2 : ℝ}
    (hx0 : 0 ≤ x0) (hx01 : x0 ≤ x1) (hx12 : x1 ≤ x2) (hx2L : x2 ≤ L)
    (hy0L : 0 ≤ y0 ∧ y0 ≤ L) (hy2L : 0 ≤ y2 ∧ y2 ≤ L)
    (hymono : 0 ≤ (y1 - y0) * (y2 - y1))
    (h01 : 4 ≤ (x0 - x1) ^ 2 + (y0 - y1) ^ 2)
    (h12 : 4 ≤ (x1 - x2) ^ 2 + (y1 - y2) ^ 2) :
    (Real.sqrt 2 + Real.sqrt 6) / 2 ≤ L := by
  have hL0 : 0 ≤ L := by linarith
  have hx : (x0 - x2) ^ 2 ≤ L ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ L - (x2 - x0) by linarith)
                               (show 0 ≤ L + (x2 - x0) by linarith)]
  have hy : (y0 - y2) ^ 2 ≤ L ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ L - (y2 - y0) by linarith)
                               (show 0 ≤ L + (y2 - y0) by linarith)]
  have h8 : 8 ≤ (x0 - x2) ^ 2 + (y0 - y2) ^ 2 := by
    nlinarith only [h01, h12, hymono, mul_nonneg (show 0 ≤ x1 - x0 by linarith)
                                                 (show 0 ≤ x2 - x1 by linarith)]
  have h4L2 : 4 ≤ L ^ 2 := by linarith
  have h3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3lt2 : Real.sqrt 3 < 2 := by nlinarith only [h3sq, Real.sqrt_nonneg 3]
  have hsum := sqrt_two_add_sqrt_six_sq
  have h2n : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h6n : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  by_contra! hL
  have hd : 0 < (Real.sqrt 2 + Real.sqrt 6) / 2 - L := by linarith
  have hs : 0 < (Real.sqrt 2 + Real.sqrt 6) / 2 + L := by linarith
  nlinarith only [mul_pos hd hs, hsum, h3lt2, h4L2]

private lemma sorted_x_case {L x0 x1 x2 y0 y1 y2 : ℝ}
    (hx0 : 0 ≤ x0) (hx01 : x0 ≤ x1) (hx12 : x1 ≤ x2) (hx2L : x2 ≤ L)
    (hy0 : 0 ≤ y0 ∧ y0 ≤ L) (hy1 : 0 ≤ y1 ∧ y1 ≤ L) (hy2 : 0 ≤ y2 ∧ y2 ≤ L)
    (h01 : 4 ≤ (x0 - x1) ^ 2 + (y0 - y1) ^ 2)
    (h12 : 4 ≤ (x1 - x2) ^ 2 + (y1 - y2) ^ 2)
    (h02 : 4 ≤ (x0 - x2) ^ 2 + (y0 - y2) ^ 2) :
    (Real.sqrt 2 + Real.sqrt 6) / 2 ≤ L := by
  rcases le_total y0 y1 with hy01 | hy10
  · rcases le_total y1 y2 with hy12 | hy21
    · exact monotone_y_case hx0 hx01 hx12 hx2L hy0 hy2
        (mul_nonneg (by linarith) (by linarith)) h01 h12
    · rcases le_total y0 y2 with hy02 | hy20
      · exact ordered_case (x0 := L - x2) (x1 := L - x1) (x2 := L - x0)
          (y0 := L - y2) (y1 := L - y1) (y2 := L - y0)
          (by linarith) (by linarith) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith) (by linarith)
          (by nlinarith only [h12]) (by nlinarith only [h01]) (by nlinarith only [h02])
      · exact ordered_case (x0 := x0) (x1 := x1) (x2 := x2)
          (y0 := L - y0) (y1 := L - y1) (y2 := L - y2)
          hx0 hx01 hx12 hx2L
          (by linarith) (by linarith) (by linarith) (by linarith)
          (by nlinarith only [h01]) (by nlinarith only [h12]) (by nlinarith only [h02])
  · rcases le_total y1 y2 with hy12 | hy21
    · rcases le_total y0 y2 with hy02 | hy20
      · exact ordered_case hx0 hx01 hx12 hx2L hy1.1 hy10 hy02 hy2.2 h01 h12 h02
      · exact ordered_case (x0 := L - x2) (x1 := L - x1) (x2 := L - x0)
          (y0 := y2) (y1 := y1) (y2 := y0)
          (by linarith) (by linarith) (by linarith) (by linarith)
          hy1.1 hy12 hy20 hy0.2
          (by nlinarith only [h12]) (by nlinarith only [h01]) (by nlinarith only [h02])
    · exact monotone_y_case hx0 hx01 hx12 hx2L hy0 hy2
        (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) h01 h12

private lemma three_points_bound {L : ℝ} {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ L) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ L)
    (hsep : ∀ i j, i ≠ j → 4 ≤ (x i - x j) ^ 2 + (y i - y j) ^ 2) :
    (Real.sqrt 2 + Real.sqrt 6) / 2 ≤ L := by
  have s01 : 4 ≤ (x 0 - x 1) ^ 2 + (y 0 - y 1) ^ 2 := hsep 0 1 (by decide)
  have s10 : 4 ≤ (x 1 - x 0) ^ 2 + (y 1 - y 0) ^ 2 := hsep 1 0 (by decide)
  have s02 : 4 ≤ (x 0 - x 2) ^ 2 + (y 0 - y 2) ^ 2 := hsep 0 2 (by decide)
  have s20 : 4 ≤ (x 2 - x 0) ^ 2 + (y 2 - y 0) ^ 2 := hsep 2 0 (by decide)
  have s12 : 4 ≤ (x 1 - x 2) ^ 2 + (y 1 - y 2) ^ 2 := hsep 1 2 (by decide)
  have s21 : 4 ≤ (x 2 - x 1) ^ 2 + (y 2 - y 1) ^ 2 := hsep 2 1 (by decide)
  rcases le_total (x 0) (x 1) with h01 | h10
  · rcases le_total (x 1) (x 2) with h12 | h21
    · exact sorted_x_case (hx 0).1 h01 h12 (hx 2).2 (hy 0) (hy 1) (hy 2) s01 s12 s02
    · rcases le_total (x 0) (x 2) with h02 | h20
      · exact sorted_x_case (hx 0).1 h02 h21 (hx 1).2 (hy 0) (hy 2) (hy 1) s02 s21 s01
      · exact sorted_x_case (hx 2).1 h20 h01 (hx 1).2 (hy 2) (hy 0) (hy 1) s20 s01 s21
  · rcases le_total (x 0) (x 2) with h02 | h20
    · exact sorted_x_case (hx 1).1 h10 h02 (hx 2).2 (hy 1) (hy 0) (hy 2) s10 s02 s12
    · rcases le_total (x 1) (x 2) with h12 | h21
      · exact sorted_x_case (hx 1).1 h12 h20 (hx 0).2 (hy 1) (hy 2) (hy 0) s12 s20 s10
      · exact sorted_x_case (hx 2).1 h21 h10 (hx 0).2 (hy 2) (hy 1) (hy 0) s21 s10 s20

/-- `s(3) ≥ 2 + √2 / 2 + √6 / 2`. -/
theorem lower_three : RadicalLowerBound 3 [(4, 1), (1, 2), (1, 6)] 2 := by
  have hrad : radical [(4, 1), (1, 2), (1, 6)] 2 = 2 + (Real.sqrt 2 + Real.sqrt 6) / 2 := by
    unfold radical
    norm_num
    ring
  rw [RadicalLowerBound, hrad]
  intro s c hc
  let x : Fin 3 → ℝ := fun i => c i 0 - 1
  let y : Fin 3 → ℝ := fun i => c i 1 - 1
  have hx : ∀ i, 0 ≤ x i ∧ x i ≤ s - 2 := by
    intro i
    obtain ⟨h0, h1, -, -⟩ := center_bounds (hc.2.1 i)
    exact ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
  have hy : ∀ i, 0 ≤ y i ∧ y i ≤ s - 2 := by
    intro i
    obtain ⟨-, -, h0, h1⟩ := center_bounds (hc.2.1 i)
    exact ⟨by dsimp [y]; linarith, by dsimp [y]; linarith⟩
  have hsep : ∀ i j, i ≠ j → 4 ≤ (x i - x j) ^ 2 + (y i - y j) ^ 2 := by
    intro i j hij
    have h4 := four_le_dist_sq hc hij
    dsimp [x, y]
    linarith only [h4]
  have hL := three_points_bound hx hy hsep
  linarith

end LeapsInBounds.Proofs.CircleInSquare3
