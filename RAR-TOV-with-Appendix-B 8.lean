import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 2000000
-- Preserve the unfolding behavior used by the original proof scripts.
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# RAR/Michie--King kinetics, regular-center TOV existence, and the filled barrier

Companion to RAR-TOV-complete-with-Appendix-B.tex (14-page manuscript).
Target: Lean 4.35.0-rc3 / Mathlib commit 5e72202a29439c40e312324b7ad3cfe0de53ddec.

STATUS: kinetic differentiation, endpoint EOS asymptotics, and local
regular-center TOV existence are proved from the explicit kinetic integrals
under physical parameter inequalities. The constructed solution has positive
mass, decreasing density, the strict phase wedge, and proved center expansions.
The global barrier theorems retain their explicit ODE-path hypotheses.
The sharper scalar root now has a proved existence/uniqueness theorem and a
certified rational enclosure, connected to the original potentials below. There are no unfinished proof placeholders or new axiom declarations;
remaining scope is identified below.

Formalized below:
* moment algebra from positive moments and the Cauchy--Schwarz inequality;
* the global slope envelope and k = 1/sqrt(3) comparison polynomial;
* pointwise domination of the nonlinear vertical TOV field;
* the corrected Lyapunov coefficients and quadratic decay identity;
* derivatives of the logarithmic potentials and the filled potential,
  including both max junctions;
* the signs on the filled barrier's horizontal, upper, and vertical sides;
* a scalar fencing theorem, using Mathlib's mean-value/fencing theorem;
* the filled-level geometry and the scalar extent of its sublevel;
* global compactness and the sharper diagonal bound for ODE paths,
  conditional on admissible moments, with a certified sharper root;
* integral Cauchy--Schwarz with explicit integrability hypotheses;
* exact definitions of the Appendix B distributions and kinetic integrals;
* the actual occupation and cutoff derivatives, including transport;
* differentiation of moving-cutoff A and B, with a proved zero endpoint term;
* the integrability of C at q=0, positivity, and kinetic Cauchy--Schwarz;
* density and pressure derivatives and the actual EOS slope ratio;
* construction of Moments from those exact integrals, and transfer of the
  slope envelope and comparator domination to the actual EOS;
* dominated convergence for the rescaled kinetic integrals, including the
  integrable singular C kernel, and exact low-density coefficients;
* ρ ~ ρ₀u^(5/2), P ~ P₀u^(7/2), and the 7/5 polytropic law;
* w/u -> 2κ/7, a/u -> 2κ/5, and a/w -> 7/5 at vacuum;
* relativistic density/pressure coefficients, density divergence, and
  P ~ (c²/3)ρ, with w,a -> 1/3;
* C = O(log(1/δ)), δ=1−κu, with a proved logarithmic upper bound;
* C¹ regularity of density, mass-unit pressure, and the interior TOV field;
* local physical interior existence with the radius component fixed;
* a Banach contraction construction at the singular regular center;
* actual mass, potential, and pressure TOV equations and a horizon margin;
* positive mass, strictly decreasing density, and the strict wedge 0<y<3x;
* the cubic mass expansion, quadratic phase expansions, and y/x -> 3;
* existence and uniqueness of the sharper scalar root and the certified
  interval 0.6734385928 < Xsharp < 0.6734385929;
* a numerical compactness corollary with the scalar-root hypothesis discharged.

Not certified in this file: the slide-to-energy normalization/change of
variables, global maximal continuation or existence of a finite vacuum surface,
the application of the global phase barrier to that maximal branch, or the
simpler Lambert/barrier root. These are identified at the end. The sharper
root is certified to the interval above, not equated to a finite decimal.
The EOS differentiation theorems assume only κ>0, χ≥0, u>0, and 1−κu>0;
ratio/comparator statements also require a nonzero kinetic normalization.

Run in the pinned Mathlib project:
`lake env lean RAR-TOV-with-Appendix-B.lean`.

Existence theorem: `RARTOV.AppendixB.exists_physical_regular_TOV`.
It constructs a regular-center solution for every uc with 0<uc and κuc<1,
assuming κ,G,mf,c,hp>0 and χ≥0.
Barrier theorem: `RARTOV.moments_path_diagonal_compactness`.
It bounds x = 2Gm/(rc^2) by the root X of U(X)+J(X)=level.
The kinetic EOS is identified by `AppendixB.kineticMoments` and
`AppendixB.kinetic_EOS_field_domination`. Solution properties remain explicit hypotheses. The numerical corollary
`moments_path_diagonal_compactness_certified` uses the proved scalar root. No trapping-region or chain-rule assumption is
required by this theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace RARTOV

/-! ## 1. Kinetic moment algebra -/

structure Moments where
  A : ℝ
  B : ℝ
  C : ℝ
  A_pos : 0 < A
  B_pos : 0 < B
  C_nonneg : 0 ≤ C
  cauchySchwarz : B ^ 2 ≤ A * C

namespace Moments

def w (m : Moments) : ℝ := m.A / (3 * (m.A + m.B))
def a (m : Moments) : ℝ := (4 * m.A / 3 + m.B) / (4 * m.A + 5 * m.B + m.C)

theorem densityDen_pos (m : Moments) : 0 < 3 * (m.A + m.B) := by
  have := m.A_pos
  have := m.B_pos
  positivity

theorem slopeDen_pos (m : Moments) : 0 < 4 * m.A + 5 * m.B + m.C := by
  have := m.A_pos
  have := m.B_pos
  have := m.C_nonneg
  positivity

theorem w_pos (m : Moments) : 0 < m.w := by
  exact div_pos m.A_pos m.densityDen_pos

theorem w_lt_one_third (m : Moments) : m.w < 1 / 3 := by
  rw [w, div_lt_iff₀ m.densityDen_pos]
  nlinarith [m.B_pos]

theorem a_pos (m : Moments) : 0 < m.a := by
  unfold a
  have := m.A_pos
  have := m.B_pos
  exact div_pos (by positivity) m.slopeDen_pos

theorem a_lt_one_third (m : Moments) : m.a < 1 / 3 := by
  rw [a, div_lt_iff₀ m.slopeDen_pos]
  nlinarith [m.B_pos, m.C_nonneg]

/-- The RHS of the envelope, written directly in terms of moments. -/
theorem envelope_identity (m : Moments) :
    3 * m.w * (1 + m.w) / (1 + 9 * m.w) =
    m.A * (4 * m.A + 3 * m.B) / (3 * (m.A + m.B) * (4 * m.A + m.B)) := by
  have hAB : m.A + m.B ≠ 0 := ne_of_gt (add_pos m.A_pos m.B_pos)
  have h4 : 4 * m.A + m.B ≠ 0 := by
    have := m.A_pos
    have := m.B_pos
    positivity
  have hw : 1 + 9 * m.w ≠ 0 := by have := m.w_pos; positivity
  have h9 : 1 + 9 * m.w = (4 * m.A + m.B) / (m.A + m.B) := by
    unfold w
    field_simp [hAB]
    ring
  rw [h9]
  unfold w
  field_simp [hAB, h4]
  ring

/-- The global kinetic slope estimate, conditional on the moment hypotheses. -/
theorem slope_envelope (m : Moments) : m.a ≤ 3 * m.w * (1 + m.w) / (1 + 9 * m.w) := by
  rw [m.envelope_identity]
  unfold a
  have hden : 0 < 3 * (m.A + m.B) * (4 * m.A + m.B) := by
    have := m.A_pos
    have := m.B_pos
    positivity
  rw [div_le_div_iff₀ m.slopeDen_pos hden]
  have hprod : 0 ≤ (4 * m.A + 3 * m.B) * (m.A * m.C - m.B ^ 2) := by
    apply mul_nonneg
    · have := m.A_pos; have := m.B_pos; positivity
    · linarith [m.cauchySchwarz]
  nlinarith

end Moments

/-! ## 2. The comparator and its exact polynomial certificate -/

def kStar : ℝ := 1 / Real.sqrt 3

theorem kStar_pos : 0 < kStar := by unfold kStar; positivity

theorem kStar_square : 3 * kStar ^ 2 = 1 := by
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  unfold kStar
  field_simp
  exact hs.symm

theorem one_third_lt_kStar : (1 : ℝ) / 3 < kStar := by
  nlinarith [kStar_pos, kStar_square]

/-- Exact square identity behind the k-star comparison; no maximization is assumed. -/
theorem comparison_polynomial (k w : ℝ) (hk : 0 < k) (hks : 3 * k ^ 2 = 1) :
    0 ≤ k * (1 + 9 * w) * (1 + 3 * w) - 3 * w * (1 + k) * (1 + 3 * k) := by
  have hkw := congrArg (fun t : ℝ => t * w) hks
  have hkk := congrArg (fun t : ℝ => t * k) hks
  try dsimp at hkw hkk
  have heq : k * (1 + 9 * w) * (1 + 3 * w) -
      3 * w * (1 + k) * (1 + 3 * k) = 3 * k * (3 * w - k) ^ 2 := by
    nlinarith [hkw, hkk]
  rw [heq]
  positivity

theorem envelope_to_comparator (k w : ℝ) (hk : 0 < k)
    (hks : 3 * k ^ 2 = 1) (hw : 0 ≤ w) :
    3 * w * (1 + w) / (1 + 9 * w) ≤
    k * (1 + w) * (1 + 3 * w) / ((1 + k) * (1 + 3 * k)) := by
  have hd1 : 0 < 1 + 9 * w := by positivity
  have hd2 : 0 < (1 + k) * (1 + 3 * k) := by positivity
  rw [div_le_div_iff₀ hd1 hd2]
  have h := mul_nonneg (comparison_polynomial k w hk hks) (show 0 ≤ 1 + w by positivity)
  nlinarith

/-- Version with no fractions in the EOS comparison hypothesis. -/
theorem moments_comparator_bound (m : Moments) :
    m.a * (1 + kStar) * (1 + 3 * kStar) ≤
    kStar * (1 + m.w) * (1 + 3 * m.w) := by
  have h := le_trans m.slope_envelope
    (envelope_to_comparator kStar m.w kStar_pos kStar_square (le_of_lt m.w_pos))
  have hd : 0 < (1 + kStar) * (1 + 3 * kStar) := by have := kStar_pos; positivity
  rw [le_div_iff₀ hd] at h
  simpa [mul_assoc] using h

/-! ## 3. TOV vector fields and the physical wedge -/

def nonlinearField (w a x y : ℝ) : ℝ :=
  y * (2 - (1 + w) / (2 * a) * ((x + w * y) / (1 - x)))

def linearField (k x y : ℝ) : ℝ :=
  y * (2 - (1 + k) / (2 * k) * ((x + k * y) / (1 - x)))

/-- Wedge geometry supplies the worst-case y/x = 3 comparison. -/
theorem wedge_cross_comparison (k w x y : ℝ) (hwk : w ≤ k) (hwed : y ≤ 3 * x) :
    (x + k * y) * (1 + 3 * w) ≤ (x + w * y) * (1 + 3 * k) := by
  have h := mul_nonneg (sub_nonneg.mpr hwk) (sub_nonneg.mpr hwed)
  nlinarith

theorem field_domination (k w a x y : ℝ)
    (hk : 0 < k) (hw : 0 ≤ w) (hwk : w ≤ k) (ha : 0 < a)
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 ≤ y) (hwed : y ≤ 3 * x)
    (hEOS : a * (1 + k) * (1 + 3 * k) ≤ k * (1 + w) * (1 + 3 * w)) :
    nonlinearField w a x y ≤ linearField k x y := by
  have hxy : 0 ≤ x + k * y := by positivity
  have h13 : 0 < 1 + 3 * k := by positivity
  have h1w : 0 ≤ k * (1 + w) := by positivity
  have hcross := wedge_cross_comparison k w x y hwk hwed
  have hleft := mul_le_mul_of_nonneg_right hEOS hxy
  have hright := mul_le_mul_of_nonneg_left hcross h1w
  have hbase : a * (1 + k) * (x + k * y) ≤ k * (1 + w) * (x + w * y) := by
    have hm : (a * (1 + k) * (x + k * y)) * (1 + 3 * k) ≤
        (k * (1 + w) * (x + w * y)) * (1 + 3 * k) := by
      nlinarith [hleft, hright]
    exact (mul_le_mul_iff_of_pos_right h13).mp hm
  have hxden : 0 < 1 - x := sub_pos.mpr hx1
  have hdenA : 0 < 2 * a * (1 - x) := by positivity
  have hdenK : 0 < 2 * k * (1 - x) := by positivity
  have hdr : (1 + k) * (x + k * y) / (2 * k * (1 - x)) ≤
      (1 + w) * (x + w * y) / (2 * a * (1 - x)) := by
    rw [div_le_div_iff₀ hdenK hdenA]
    have h := mul_le_mul_of_nonneg_right hbase (show 0 ≤ 2 * (1 - x) by positivity)
    nlinarith
  have hrewriteA : (1 + w) / (2 * a) * ((x + w * y) / (1 - x)) =
      (1 + w) * (x + w * y) / (2 * a * (1 - x)) := by rw [div_mul_div_comm]
  have hrewriteK : (1 + k) / (2 * k) * ((x + k * y) / (1 - x)) =
      (1 + k) * (x + k * y) / (2 * k * (1 - x)) := by rw [div_mul_div_comm]
  unfold nonlinearField linearField
  rw [hrewriteA, hrewriteK]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hdr 2) hy

theorem moments_field_domination (m : Moments) (x y : ℝ)
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 ≤ y) (hwed : y ≤ 3 * x) :
    nonlinearField m.w m.a x y ≤ linearField kStar x y := by
  apply field_domination kStar m.w m.a x y kStar_pos (le_of_lt m.w_pos)
      (le_of_lt (lt_trans m.w_lt_one_third one_third_lt_kStar))
      m.a_pos hx hx1 hy hwed
  exact moments_comparator_bound m

/-! ## 4. Corrected linear Lyapunov geometry -/

def z (k : ℝ) : ℝ := 4 * k / (1 + 6 * k + k ^ 2)
def xi (k : ℝ) : ℝ := 4 * k / (1 + 8 * k + 3 * k ^ 2)
def cap (k : ℝ) : ℝ := 3 * xi k
def h (k : ℝ) : ℝ := (1 + 5 * k) / (2 * k)
def b (k : ℝ) : ℝ := h k * (1 - z k)

/-- Log form equivalent to the ratio-log expression in the manuscript. -/
def U (k x : ℝ) : ℝ := h k * (z k - x) + b k * (Real.log (1 - z k) - Real.log (1 - x))
def J (k y : ℝ) : ℝ := y - z k - z k * (Real.log y - Real.log (z k))
def V (k x y : ℝ) : ℝ := U k x + J k y
def level (k : ℝ) : ℝ := J k (cap k)
def filled (k x y : ℝ) : ℝ := U k (max x (z k)) + J k (max y (z k))
def Ugrad (k x : ℝ) : ℝ := h k * (x - z k) / (1 - x)
def Jgrad (k y : ℝ) : ℝ := 1 - z k / y

theorem z_pos (k : ℝ) (hk : 0 < k) : 0 < z k := by unfold z; positivity

theorem z_lt_one (k : ℝ) (hk : 0 < k) : z k < 1 := by
  unfold z
  have hd : 0 < 1 + 6 * k + k ^ 2 := by positivity
  rw [div_lt_one hd]
  nlinarith [sq_nonneg k]

theorem h_pos (k : ℝ) (hk : 0 < k) : 0 < h k := by unfold h; positivity

theorem b_pos (k : ℝ) (hk : 0 < k) : 0 < b k := by
  exact mul_pos (h_pos k hk) (sub_pos.mpr (z_lt_one k hk))

theorem xi_pos (k : ℝ) (hk : 0 < k) : 0 < xi k := by unfold xi; positivity

theorem xi_lt_z (k : ℝ) (hk : 0 < k) : xi k < z k := by
  have hd1 : 0 < 1 + 8 * k + 3 * k ^ 2 := by positivity
  have hd2 : 0 < 1 + 6 * k + k ^ 2 := by positivity
  unfold xi z
  rw [div_lt_div_iff₀ hd1 hd2]
  have hm : 0 < 8 * k ^ 2 * (1 + k) := by positivity
  nlinarith

theorem z_lt_cap (k : ℝ) (hk : 0 < k) : z k < cap k := by
  have hd1 : 0 < 1 + 8 * k + 3 * k ^ 2 := by positivity
  have hd2 : 0 < 1 + 6 * k + k ^ 2 := by positivity
  unfold z cap xi
  rw [← mul_div_assoc, div_lt_div_iff₀ hd2 hd1]
  have hm : 0 < 8 * k * (1 + 5 * k) := by positivity
  nlinarith

@[simp] theorem U_at_z (k : ℝ) : U k (z k) = 0 := by simp [U]
@[simp] theorem J_at_z (k : ℝ) : J k (z k) = 0 := by simp [J]

theorem J_nonneg (k y : ℝ) (hk : 0 < k) (hy : 0 < y) : 0 ≤ J k y := by
  have hz := z_pos k hk
  have hlog := Real.log_le_sub_one_of_pos (div_pos hy hz)
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hz)] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt hz)
  have heq : z k * (y / z k - 1) = y - z k := by field_simp
  rw [heq] at hm
  unfold J
  linarith

/-- Direct differentiation, so the gradients are proved rather than postulated. -/
theorem hasDerivAt_U (k x : ℝ) (hx1 : x < 1) : HasDerivAt (U k) (Ugrad k x) x := by
  have hn : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hlin : HasDerivAt (fun t : ℝ => z k - t) (-1) x := by
    convert (hasDerivAt_const x (z k)).sub (hasDerivAt_id x) using 1 <;> first | rfl | ring
  have hlog : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - x)) x := by
    simpa using ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log hn
  have hfull := (hlin.const_mul (h k)).add
    (((hasDerivAt_const x (Real.log (1 - z k))).sub hlog).const_mul (b k))
  convert hfull using 1 <;> try rfl
  unfold Ugrad b
  field_simp [hn]
  ring

theorem hasDerivAt_J (k y : ℝ) (hy : 0 < y) : HasDerivAt (J k) (Jgrad k y) y := by
  have hlog := (Real.hasDerivAt_log (ne_of_gt hy)).sub_const (Real.log (z k))
  have hfull := ((hasDerivAt_id y).sub_const (z k)).sub (hlog.const_mul (z k))
  convert hfull using 1 <;> try rfl

/-- Correcting the printed coefficient: this equality vanishes only at k=1. -/
def printedB (k : ℝ) : ℝ :=
  (1 + k) / (2 * k) * ((4 * k + (1 + k) ^ 3) / (4 * k + (1 + k) ^ 2))

theorem coefficient_correction (k : ℝ) (hk : 0 < k) :
    printedB k - b k = (1 + k) * (1 - k) ^ 2 / (2 * (1 + 6 * k + k ^ 2)) := by
  have hn : k ≠ 0 := ne_of_gt hk
  have hd : 1 + 6 * k + k ^ 2 ≠ 0 := by positivity
  have hq : 4 * k + (1 + k) ^ 2 ≠ 0 := by positivity
  unfold printedB b h z
  field_simp
  ring

/-- The exact quadratic identity for the linear field. -/
theorem lyapunov_identity (k x y : ℝ) (hk : 0 < k) (hx1 : x < 1) (hy : 0 < y) :
    (1 - x) * (Ugrad k x * (y - x) + Jgrad k y * linearField k x y) =
      -h k * (x - z k) ^ 2 - (1 + k) / 2 * (y - z k) ^ 2 := by
  have hkn : k ≠ 0 := ne_of_gt hk
  have hxn : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hyn : y ≠ 0 := ne_of_gt hy
  have hdn : 1 + 6 * k + k ^ 2 ≠ 0 := by positivity
  unfold Ugrad Jgrad linearField h z
  field_simp
  ring

/-- Transfer identity for any vertical component f. -/
theorem lyapunov_transfer_identity (k x y f : ℝ) (hk : 0 < k)
    (hx1 : x < 1) (hy : 0 < y) :
    (1 - x) * (Ugrad k x * (y - x) + Jgrad k y * f) =
      -h k * (x - z k) ^ 2 - (1 + k) / 2 * (y - z k) ^ 2 +
        (1 - x) * Jgrad k y * (f - linearField k x y) := by
  have hid := lyapunov_identity k x y hk hx1 hy
  nlinarith [hid]



/-- The x-potential is strictly increasing to the right of the equilibrium. -/
theorem U_strictMonoOn (k : ℝ) (hk : 0 < k) :
    StrictMonoOn (U k) (Ico (z k) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico (z k) 1)
  · intro x hx
    exact (hasDerivAt_U k x hx.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    rw [(hasDerivAt_U k x hx.2).deriv]
    unfold Ugrad
    exact div_pos (mul_pos (h_pos k hk) (sub_pos.mpr hx.1)) (sub_pos.mpr hx.2)

theorem J_strictMonoOn (k : ℝ) (hk : 0 < k) :
    StrictMonoOn (J k) (Ici (z k)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (z k))
  · intro y hy
    exact (hasDerivAt_J k y (lt_of_lt_of_le (z_pos k hk) hy)).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hpos : 0 < y := lt_trans (z_pos k hk) hy
    rw [(hasDerivAt_J k y hpos).deriv]
    unfold Jgrad
    have hd : z k / y < 1 := (div_lt_one hpos).mpr hy
    linarith

theorem level_pos (k : ℝ) (hk : 0 < k) : 0 < level k := by
  have hh := J_strictMonoOn k hk (show z k ∈ Ici (z k) by simp)
    (show cap k ∈ Ici (z k) from (z_lt_cap k hk).le) (z_lt_cap k hk)
  simpa [level] using hh

/-- Gluing at the max junction is legitimate when the original derivative is zero.
This generic lemma supplies the C1 calculation needed by the filled barrier. -/
theorem hasDerivAt_truncate (f : ℝ → ℝ) (c x d : ℝ)
    (hx : HasDerivAt f d x) (hc : HasDerivAt f 0 c) :
    HasDerivAt (fun t => f (max t c)) (if c < x then d else 0) x := by
  rcases lt_trichotomy x c with hlt | heq | hgt
  · have hev : (fun t => f (max t c)) =ᶠ[𝓝 x] (fun _ => f c) := by
      filter_upwards [eventually_lt_nhds hlt] with t ht
      simp [max_eq_right (le_of_lt ht)]
    simpa [not_lt.mpr (le_of_lt hlt)] using (hasDerivAt_const x (f c)).congr_of_eventuallyEq hev
  · subst x
    have hl : HasDerivWithinAt (fun t => f (max t c)) 0 (Iic c) c := by
      apply (hasDerivAt_const c (f c)).hasDerivWithinAt.congr
      · intro t ht; simp [max_eq_right (show t ≤ c from ht)]
      · simp
    have hr : HasDerivWithinAt (fun t => f (max t c)) 0 (Ici c) c := by
      apply hc.hasDerivWithinAt.congr
      · intro t ht; simp [max_eq_left (show c ≤ t from ht)]
      · simp
    have hu := hl.union hr
    rw [Iic_union_Ici] at hu
    simpa using hu.hasDerivAt (by simp)
  · have hev : (fun t => f (max t c)) =ᶠ[𝓝 x] f := by
      filter_upwards [eventually_gt_nhds hgt] with t ht
      simp [max_eq_left (le_of_lt ht)]
    simpa [hgt] using hx.congr_of_eventuallyEq hev

/-! ## 5. Boundary orientation -/

theorem Jgrad_nonneg (k y : ℝ) (hy : 0 < y) (hzy : z k ≤ y) : 0 ≤ Jgrad k y := by
  unfold Jgrad
  have hd : z k / y ≤ 1 := (div_le_one hy).mpr hzy
  linarith

theorem upper_boundary_negative (k x y f : ℝ) (hk : 0 < k)
    (hx1 : x < 1) (hy : 0 < y) (hzy : z k ≤ y)
    (hfield : f ≤ linearField k x y)
    (hne : x ≠ z k ∨ y ≠ z k) :
    Ugrad k x * (y - x) + Jgrad k y * f < 0 := by
  have hsq : -h k * (x - z k) ^ 2 - (1 + k) / 2 * (y - z k) ^ 2 < 0 := by
    have hh := h_pos k hk
    have hs1 := sq_nonneg (x - z k)
    have hs2 := sq_nonneg (y - z k)
    rcases hne with hx | hy'
    · have hp : 0 < (x - z k) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
      have hprod := mul_pos hh hp
      have hprod2 : 0 ≤ (1 + k) / 2 * (y - z k) ^ 2 := by positivity
      linarith
    · have hp : 0 < (y - z k) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hy')
      have hprod : 0 < (1 + k) / 2 * (y - z k) ^ 2 := by positivity
      have hprod1 : 0 ≤ h k * (x - z k) ^ 2 := by positivity
      linarith
  have hc : (1 - x) * Jgrad k y * (f - linearField k x y) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (le_of_lt (sub_pos.mpr hx1)) (Jgrad_nonneg k y hy hzy))
      (sub_nonpos.mpr hfield)
  have hid := lyapunov_transfer_identity k x y f hk hx1 hy
  have hneg : (1 - x) * (Ugrad k x * (y - x) + Jgrad k y * f) < 0 := by
    rw [hid]
    linarith
  by_contra hn
  have hh : 0 ≤ Ugrad k x * (y - x) + Jgrad k y * f := le_of_not_gt hn
  have hm := mul_nonneg (le_of_lt (sub_pos.mpr hx1)) hh
  linarith

theorem cap_nullcline (k : ℝ) (hk : 0 < k) :
    4 * k - (1 + 5 * k) * xi k - k * (1 + k) * cap k = 0 := by
  have hd : 1 + 8 * k + 3 * k ^ 2 ≠ 0 := by positivity
  unfold cap xi
  field_simp
  ring

theorem linearField_fraction (k x y : ℝ) (hk : 0 < k) (hx1 : x < 1) :
    linearField k x y =
    y * (4 * k - (1 + 5 * k) * x - k * (1 + k) * y) / (2 * k * (1 - x)) := by
  have hkn : k ≠ 0 := ne_of_gt hk
  have hxn : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  unfold linearField
  field_simp [hkn, hxn]
  ring_nf


/-- Horizontal cap: the strict physical wedge excludes the tangency point. -/
theorem cap_boundary_negative (k x f : ℝ) (hk : 0 < k) (hx1 : x < 1)
    (hwed : cap k < 3 * x) (hfield : f ≤ linearField k x (cap k)) :
    Jgrad k (cap k) * f < 0 := by
  have hy : 0 < cap k := by unfold cap; exact mul_pos (by norm_num) (xi_pos k hk)
  have hxi : xi k < x := by unfold cap at hwed; linarith
  have hnull := cap_nullcline k hk
  have hprod : 0 < (1 + 5 * k) * (x - xi k) := by
    exact mul_pos (by positivity) (sub_pos.mpr hxi)
  have hn : 4 * k - (1 + 5 * k) * x - k * (1 + k) * cap k < 0 := by
    nlinarith [hnull]
  have hf : linearField k x (cap k) < 0 := by
    rw [linearField_fraction k x (cap k) hk hx1]
    have hxden : 0 < 1 - x := sub_pos.mpr hx1
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hy hn) (by positivity)
  have hg : 0 < Jgrad k (cap k) := by
    unfold Jgrad
    have hdiv : z k / cap k < 1 := (div_lt_one hy).mpr (z_lt_cap k hk)
    linarith
  exact mul_neg_of_pos_of_neg hg (lt_of_le_of_lt hfield hf)

/-- Right vertical boundary, including points below the Lyapunov oval. -/
theorem right_boundary_negative (k x y : ℝ) (hk : 0 < k)
    (hzx : z k < x) (hx1 : x < 1) (hyz : y ≤ z k) :
    Ugrad k x * (y - x) < 0 := by
  have hU : 0 < Ugrad k x := by
    unfold Ugrad
    exact div_pos (mul_pos (h_pos k hk) (sub_pos.mpr hzx)) (sub_pos.mpr hx1)
  exact mul_neg_of_pos_of_neg hU (by linarith)

/-- Algebraic gradient of the filled potential along x' = y-x, y' = f.
The chain rule identifying this expression with the derivative of `filled`
is an explicit hypothesis in the path-level result below. -/
def filledRate (k x y f : ℝ) : ℝ :=
  (if z k < x then Ugrad k x * (y - x) else 0) +
  (if z k < y then Jgrad k y * f else 0)


/-- Chain rule for the actual filled potential, including both max junctions. -/
theorem hasDerivAt_filled_path (k t : ℝ) (x y : ℝ → ℝ) (f : ℝ)
    (hk : 0 < k) (hx1 : x t < 1) (hypos : 0 < y t)
    (hx : HasDerivAt x (y t - x t) t) (hy : HasDerivAt y f t) :
    HasDerivAt (fun s => filled k (x s) (y s))
      (filledRate k (x t) (y t) f) t := by
  have hz := z_pos k hk
  have hUz : HasDerivAt (U k) 0 (z k) := by
    simpa [Ugrad] using hasDerivAt_U k (z k) (z_lt_one k hk)
  have hJz : HasDerivAt (J k) 0 (z k) := by
    simpa [Jgrad, ne_of_gt hz] using hasDerivAt_J k (z k) hz
  have hU := (hasDerivAt_truncate (U k) (z k) (x t) (Ugrad k (x t))
    (hasDerivAt_U k (x t) hx1) hUz).comp t hx
  have hJ := (hasDerivAt_truncate (J k) (z k) (y t) (Jgrad k (y t))
    (hasDerivAt_J k (y t) hypos) hJz).comp t hy
  convert hU.add hJ using 1 <;> try rfl
  unfold filledRate
  split_ifs <;> ring

/-- A normalized boundary description with no trajectory assumptions. -/
structure BoundaryGeometry (k E x y : ℝ) : Prop where
  horizontal : x ≤ z k → y = cap k
  lower : y ≤ z k → z k < x
  upper : z k ≤ x → z k ≤ y → x ≠ z k ∨ y ≠ z k


/-- The boundary certificates follow from the logarithmic level equation itself. -/
theorem boundaryGeometry_of_level (k x y : ℝ) (hk : 0 < k)
    (heq : filled k x y = level k) : BoundaryGeometry k (level k) x y := by
  have hE := level_pos k hk
  constructor
  · intro hx
    have hj : J k (max y (z k)) = J k (cap k) := by
      simpa [filled, max_eq_right hx, level] using heq
    have hmax : max y (z k) = cap k := by
      exact (J_strictMonoOn k hk).injOn
        (show max y (z k) ∈ Ici (z k) by change z k ≤ max y (z k); exact le_max_right y (z k))
        (show cap k ∈ Ici (z k) from (z_lt_cap k hk).le) hj
    have hzy : z k < y := by
      by_contra hn
      have hyz : y ≤ z k := le_of_not_gt hn
      rw [max_eq_right hyz] at hmax
      have hzcap := z_lt_cap k hk
      linarith
    simpa [max_eq_left hzy.le] using hmax
  · intro hyz
    by_contra hn
    have hxz : x ≤ z k := le_of_not_gt hn
    have hz : filled k x y = 0 := by
      simp [filled, max_eq_right hxz, max_eq_right hyz]
    linarith
  · intro _ _
    by_cases hx : x = z k
    · by_cases hy : y = z k
      · have hz : filled k x y = 0 := by simp [filled, hx, hy]
        exfalso; linarith
      · exact Or.inr hy
    · exact Or.inl hx

/-- All three signs combine into the derivative sign on the filled boundary. -/
theorem filled_boundary_negative (k E x y f : ℝ) (hk : 0 < k)
    (hx1 : x < 1) (hy : 0 < y) (hwed : y < 3 * x)
    (hfield : f ≤ linearField k x y) (hg : BoundaryGeometry k E x y) :
    filledRate k x y f < 0 := by
  by_cases hx : z k < x
  · by_cases hy' : z k < y
    · simpa [filledRate, hx, hy'] using
        upper_boundary_negative k x y f hk hx1 hy (le_of_lt hy') hfield
          (Or.inl (ne_of_gt hx))
    · have hyz : y ≤ z k := le_of_not_gt hy'
      simpa [filledRate, hx, hy'] using right_boundary_negative k x y hk hx hx1 hyz
  · have hxz : x ≤ z k := le_of_not_gt hx
    have heq := hg.horizontal hxz
    subst y
    have hzy : z k < cap k := z_lt_cap k hk
    simpa [filledRate, hx, hzy] using cap_boundary_negative k x f hk hx1 hwed hfield

/-! ## 6. Scalar fencing and path-level barriers -/

/-- The fully proved ODE fencing step. Hypotheses are right derivatives on [s0,s1). -/
theorem scalar_fence (P Pdot : ℝ → ℝ) (E s0 s1 : ℝ)
    (hcont : ContinuousOn P (Icc s0 s1))
    (hderiv : ∀ t ∈ Ico s0 s1, HasDerivWithinAt P (Pdot t) (Ici t) t)
    (hstart : P s0 ≤ E)
    (hboundary : ∀ t ∈ Ico s0 s1, P t = E → Pdot t < 0) :
    ∀ t ∈ Icc s0 s1, P t ≤ E := by
  apply image_le_of_deriv_right_lt_deriv_boundary
    (B := fun _ : ℝ => E) (B' := fun _ : ℝ => 0) hcont hderiv hstart
  · intro t; exact hasDerivAt_const t E
  · exact hboundary

/-- Sufficient regularity for applying the fencing theorem to the actual filled potential.
The actual chain rule, including the max junctions, is proved by
`hasDerivAt_filled_path`; this structure is also a reusable lower-level interface. -/
structure FilledPathData (k s0 s1 : ℝ) (x y f : ℝ → ℝ) : Prop where
  continuous : ContinuousOn (fun t => filled k (x t) (y t)) (Icc s0 s1)
  chainRule : ∀ t ∈ Ico s0 s1,
    HasDerivWithinAt (fun t => filled k (x t) (y t))
      (filledRate k (x t) (y t) (f t)) (Ici t) t
  horizonFree : ∀ t ∈ Ico s0 s1, x t < 1
  densityPositive : ∀ t ∈ Ico s0 s1, 0 < y t
  strictWedge : ∀ t ∈ Ico s0 s1, y t < 3 * x t
  comparison : ∀ t ∈ Ico s0 s1, f t ≤ linearField k (x t) (y t)

/-- Conditional global barrier: the local boundary orientation is proved above.
`geometry` is a separate logarithmic-sublevel certificate, not an invariant-set assumption. -/
theorem filled_path_barrier (k E s0 s1 : ℝ) (x y f : ℝ → ℝ) (hk : 0 < k)
    (hp : FilledPathData k s0 s1 x y f)
    (hstart : filled k (x s0) (y s0) ≤ E)
    (geometry : ∀ t ∈ Ico s0 s1, filled k (x t) (y t) = E →
      BoundaryGeometry k E (x t) (y t)) :
    ∀ t ∈ Icc s0 s1, filled k (x t) (y t) ≤ E := by
  apply scalar_fence (fun t => filled k (x t) (y t))
      (fun t => filledRate k (x t) (y t) (f t)) E s0 s1
      hp.continuous hp.chainRule hstart
  intro t ht heq
  exact filled_boundary_negative k E (x t) (y t) (f t) hk
    (hp.horizonFree t ht) (hp.densityPositive t ht) (hp.strictWedge t ht)
    (hp.comparison t ht) (geometry t ht heq)

/-- An exact, root-based compactness conclusion; this does not certify a decimal bound.
The extent certificate asks only for scalar sublevel geometry. -/
theorem compactness_from_filled_barrier (k E X s0 s1 : ℝ)
    (x y f : ℝ → ℝ) (hk : 0 < k)
    (hp : FilledPathData k s0 s1 x y f)
    (hstart : filled k (x s0) (y s0) ≤ E)
    (geometry : ∀ t ∈ Ico s0 s1, filled k (x t) (y t) = E →
      BoundaryGeometry k E (x t) (y t))
    (extent : ∀ xx yy : ℝ, filled k xx yy ≤ E → xx ≤ X) :
    ∀ t ∈ Icc s0 s1, x t ≤ X := by
  intro t ht
  exact extent (x t) (y t)
    (filled_path_barrier k E s0 s1 x y f hk hp hstart geometry t ht)


/-- The scalar extent follows from a root of U, not an assumed mass bound. -/
theorem filled_extent (k X xx yy : ℝ) (hk : 0 < k)
    (hXz : z k ≤ X) (hX1 : X < 1) (hroot : U k X = level k)
    (hxx1 : xx < 1) (hsub : filled k xx yy ≤ level k) : xx ≤ X := by
  by_contra hn
  have hXx : X < xx := lt_of_not_ge hn
  have hzx : z k < xx := lt_of_le_of_lt hXz hXx
  have hJ : 0 ≤ J k (max yy (z k)) := by
    exact J_nonneg k (max yy (z k)) hk (lt_of_lt_of_le (z_pos k hk) (le_max_right _ _))
  have hU : U k xx ≤ level k := by
    unfold filled at hsub
    rw [max_eq_left hzx.le] at hsub
    linarith
  have hstrict : U k X < U k xx :=
    U_strictMonoOn k hk (show X ∈ Ico (z k) 1 from ⟨hXz, hX1⟩)
      (show xx ∈ Ico (z k) 1 from ⟨hzx.le, hxx1⟩) hXx
  linarith

/-- Path-level compactness theorem, with actual derivatives of x and y.
No filled-potential derivative or invariant-region certificate is assumed.
The root equation specifies the bound exactly; root existence is separate. -/
theorem compactness_from_ODE (k X s0 s1 : ℝ) (x y f : ℝ → ℝ)
    (hk : 0 < k) (hXz : z k ≤ X) (hX1 : X < 1) (hroot : U k X = level k)
    (hx1 : ∀ t ∈ Icc s0 s1, x t < 1)
    (hypos : ∀ t ∈ Icc s0 s1, 0 < y t)
    (hwed : ∀ t ∈ Icc s0 s1, y t < 3 * x t)
    (hxderiv : ∀ t ∈ Icc s0 s1, HasDerivAt x (y t - x t) t)
    (hyderiv : ∀ t ∈ Icc s0 s1, HasDerivAt y (f t) t)
    (hcompare : ∀ t ∈ Icc s0 s1, f t ≤ linearField k (x t) (y t))
    (hstart : filled k (x s0) (y s0) ≤ level k) :
    ∀ t ∈ Icc s0 s1, x t ≤ X := by
  have hfilled : ∀ t ∈ Icc s0 s1,
      HasDerivAt (fun s => filled k (x s) (y s))
        (filledRate k (x t) (y t) (f t)) t := by
    intro t ht
    exact hasDerivAt_filled_path k t x y (f t) hk (hx1 t ht) (hypos t ht)
      (hxderiv t ht) (hyderiv t ht)
  have hp : FilledPathData k s0 s1 x y f := by
    constructor
    · intro t ht; exact (hfilled t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hfilled t (Ico_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht; exact hx1 t (Ico_subset_Icc_self ht)
    · intro t ht; exact hypos t (Ico_subset_Icc_self ht)
    · intro t ht; exact hwed t (Ico_subset_Icc_self ht)
    · intro t ht; exact hcompare t (Ico_subset_Icc_self ht)
  have hb := filled_path_barrier k (level k) s0 s1 x y f hk hp hstart
    (fun t _ heq => boundaryGeometry_of_level k (x t) (y t) hk heq)
  intro t ht
  exact filled_extent k X (x t) (y t) hk hXz hX1 hroot (hx1 t ht) (hb t ht)

/-- Near-center data automatically enter the filled barrier. -/
theorem near_center_inside (k xx yy : ℝ) (hk : 0 < k)
    (hx : xx ≤ z k) (hy : yy ≤ z k) : filled k xx yy < level k := by
  have hz : filled k xx yy = 0 := by simp [filled, max_eq_right hx, max_eq_right hy]
  rw [hz]
  exact level_pos k hk

/-- Compactness for the nonlinear field supplied by a family of admissible moments.
The remaining kinetic task is to construct these moments from Appendix B. -/
theorem moments_path_compactness (X s0 s1 : ℝ) (m : ℝ → Moments) (x y : ℝ → ℝ)
    (hXz : z kStar ≤ X) (hX1 : X < 1) (hroot : U kStar X = level kStar)
    (hxpos : ∀ t ∈ Icc s0 s1, 0 < x t)
    (hx1 : ∀ t ∈ Icc s0 s1, x t < 1)
    (hypos : ∀ t ∈ Icc s0 s1, 0 < y t)
    (hwed : ∀ t ∈ Icc s0 s1, y t < 3 * x t)
    (hxderiv : ∀ t ∈ Icc s0 s1, HasDerivAt x (y t - x t) t)
    (hyderiv : ∀ t ∈ Icc s0 s1,
      HasDerivAt y (nonlinearField (m t).w (m t).a (x t) (y t)) t)
    (hstartX : x s0 ≤ z kStar) (hstartY : y s0 ≤ z kStar) :
    ∀ t ∈ Icc s0 s1, x t ≤ X := by
  apply compactness_from_ODE kStar X s0 s1 x y
    (fun t => nonlinearField (m t).w (m t).a (x t) (y t))
    kStar_pos hXz hX1 hroot hx1 hypos hwed hxderiv hyderiv
  · intro t ht
    exact moments_field_domination (m t) (x t) (y t) (hxpos t ht) (hx1 t ht)
      (hypos t ht).le (hwed t ht).le
  · exact (near_center_inside kStar (x s0) (y s0) kStar_pos hstartX hstartY).le

/-- The diagonal refinement holds pointwise whenever x can increase.
It is formulated with its implicit root, without an uncertified decimal value. -/
theorem diagonal_bound_when_increasing (k X xx yy : ℝ) (hk : 0 < k)
    (hXz : z k < X) (hX1 : X < 1) (hroot : U k X + J k X = level k)
    (hxx1 : xx < 1) (hinc : xx ≤ yy) (hsub : filled k xx yy ≤ level k) : xx ≤ X := by
  by_contra hn
  have hXx : X < xx := lt_of_not_ge hn
  have hzx : z k < xx := lt_trans hXz hXx
  have hzy : z k < yy := lt_of_lt_of_le hzx hinc
  have hU : U k X < U k xx := U_strictMonoOn k hk
    (show X ∈ Ico (z k) 1 from ⟨hXz.le, hX1⟩)
    (show xx ∈ Ico (z k) 1 from ⟨hzx.le, hxx1⟩) hXx
  have hJ : J k X ≤ J k yy := (J_strictMonoOn k hk).monotoneOn
    (show X ∈ Ici (z k) from hXz.le) (show yy ∈ Ici (z k) from hzy.le)
    (le_of_lt (lt_of_lt_of_le hXx hinc))
  unfold filled at hsub
  rw [max_eq_left hzx.le, max_eq_left hzy.le] at hsub
  linarith

/-- The pointwise diagonal estimate propagates globally. If x tried to cross
any slightly larger level, y < x there, hence x' = y-x is strictly negative. -/
theorem diagonal_path_bound (k X s0 s1 : ℝ) (x y : ℝ → ℝ) (hk : 0 < k)
    (hXz : z k < X) (hX1 : X < 1) (hroot : U k X + J k X = level k)
    (hx1 : ∀ t ∈ Icc s0 s1, x t < 1)
    (hcont : ContinuousOn x (Icc s0 s1))
    (hderiv : ∀ t ∈ Ico s0 s1, HasDerivWithinAt x (y t - x t) (Ici t) t)
    (hstart : x s0 ≤ X)
    (hsub : ∀ t ∈ Icc s0 s1, filled k (x t) (y t) ≤ level k) :
    ∀ t ∈ Icc s0 s1, x t ≤ X := by
  intro t ht
  by_contra hn
  have hXt : X < x t := lt_of_not_ge hn
  let L : ℝ := (X + x t) / 2
  have hXL : X < L := by dsimp [L]; linarith
  have hLt : L < x t := by dsimp [L]; linarith
  have hbound : ∀ s ∈ Icc s0 s1, x s ≤ L := by
    apply scalar_fence x (fun s => y s - x s) L s0 s1 hcont hderiv
      (le_trans hstart hXL.le)
    intro s hs heq
    have hys : y s < x s := by
      by_contra hny
      have hdiag := diagonal_bound_when_increasing k X (x s) (y s) hk hXz hX1
        hroot (hx1 s (Ico_subset_Icc_self hs)) (le_of_not_gt hny)
        (hsub s (Ico_subset_Icc_self hs))
      rw [heq] at hdiag
      linarith
    linarith
  have hbt := hbound t ht
  linarith

/-- Sharper global compactness for a nonlinear TOV solution supplied by admissible
moments. The exact diagonal root is used; no numerical approximation is assumed. -/
theorem moments_path_diagonal_compactness (X s0 s1 : ℝ)
    (m : ℝ → Moments) (x y : ℝ → ℝ)
    (hXz : z kStar < X) (hX1 : X < 1)
    (hroot : U kStar X + J kStar X = level kStar)
    (hxpos : ∀ t ∈ Icc s0 s1, 0 < x t)
    (hx1 : ∀ t ∈ Icc s0 s1, x t < 1)
    (hypos : ∀ t ∈ Icc s0 s1, 0 < y t)
    (hwed : ∀ t ∈ Icc s0 s1, y t < 3 * x t)
    (hxderiv : ∀ t ∈ Icc s0 s1, HasDerivAt x (y t - x t) t)
    (hyderiv : ∀ t ∈ Icc s0 s1,
      HasDerivAt y (nonlinearField (m t).w (m t).a (x t) (y t)) t)
    (hstartX : x s0 ≤ z kStar) (hstartY : y s0 ≤ z kStar) :
    ∀ t ∈ Icc s0 s1, x t ≤ X := by
  let f : ℝ → ℝ := fun t => nonlinearField (m t).w (m t).a (x t) (y t)
  have hfilled : ∀ t ∈ Icc s0 s1,
      HasDerivAt (fun s => filled kStar (x s) (y s))
        (filledRate kStar (x t) (y t) (f t)) t := by
    intro t ht
    exact hasDerivAt_filled_path kStar t x y (f t) kStar_pos (hx1 t ht) (hypos t ht)
      (hxderiv t ht) (hyderiv t ht)
  have hp : FilledPathData kStar s0 s1 x y f := by
    constructor
    · intro t ht; exact (hfilled t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hfilled t (Ico_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht; exact hx1 t (Ico_subset_Icc_self ht)
    · intro t ht; exact hypos t (Ico_subset_Icc_self ht)
    · intro t ht; exact hwed t (Ico_subset_Icc_self ht)
    · intro t ht
      exact moments_field_domination (m t) (x t) (y t)
        (hxpos t (Ico_subset_Icc_self ht)) (hx1 t (Ico_subset_Icc_self ht))
        (hypos t (Ico_subset_Icc_self ht)).le (hwed t (Ico_subset_Icc_self ht)).le
  have hb := filled_path_barrier kStar (level kStar) s0 s1 x y f kStar_pos hp
    (near_center_inside kStar (x s0) (y s0) kStar_pos hstartX hstartY).le
    (fun t _ heq => boundaryGeometry_of_level kStar (x t) (y t) kStar_pos heq)
  apply diagonal_path_bound kStar X s0 s1 x y kStar_pos hXz hX1 hroot hx1
  · intro t ht; exact (hxderiv t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (hxderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  · exact le_trans hstartX hXz.le
  · exact hb

/-! ## 7. Generic integral Cauchy--Schwarz from a nonnegative quadratic -/

/-- Cauchy--Schwarz proved at the integral level. Integrability is explicit.
This lemma can be instantiated with the square roots of the kinetic kernels. -/
theorem integral_cauchy_schwarz {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ)
    (hff : Integrable (fun t => f t ^ 2) μ)
    (hfg : Integrable (fun t => f t * g t) μ)
    (hgg : Integrable (fun t => g t ^ 2) μ)
    (hA : 0 < ∫ t, f t ^ 2 ∂μ) :
    (∫ t, f t * g t ∂μ) ^ 2 ≤
      (∫ t, f t ^ 2 ∂μ) * (∫ t, g t ^ 2 ∂μ) := by
  let A : ℝ := ∫ t, f t ^ 2 ∂μ
  let B : ℝ := ∫ t, f t * g t ∂μ
  let C : ℝ := ∫ t, g t ^ 2 ∂μ
  have hpoly : (fun t => (B * f t - A * g t) ^ 2) =
      (fun t => B ^ 2 * (f t ^ 2) + (-2 * B * A) * (f t * g t) + A ^ 2 * (g t ^ 2)) := by
    funext t; ring
  have hnonneg : 0 ≤ ∫ t, (B * f t - A * g t) ^ 2 ∂μ := by
    exact integral_nonneg (fun t => sq_nonneg _)
  have h1 : Integrable (fun t => B ^ 2 * (f t ^ 2)) μ := hff.const_mul _
  have h2 : Integrable (fun t => (-2 * B * A) * (f t * g t)) μ := hfg.const_mul _
  have h3 : Integrable (fun t => A ^ 2 * (g t ^ 2)) μ := hgg.const_mul _
  have hadd : (∫ t, B ^ 2 * (f t ^ 2) + (-2 * B * A) * (f t * g t) + A ^ 2 * (g t ^ 2) ∂μ) =
      (∫ t, B ^ 2 * (f t ^ 2) + (-2 * B * A) * (f t * g t) ∂μ) +
      (∫ t, A ^ 2 * (g t ^ 2) ∂μ) := by
    simpa only [Pi.add_apply] using integral_add (h1.add h2) h3
  have hadd' : (∫ t, B ^ 2 * (f t ^ 2) + (-2 * B * A) * (f t * g t) ∂μ) =
      (∫ t, B ^ 2 * (f t ^ 2) ∂μ) + (∫ t, (-2 * B * A) * (f t * g t) ∂μ) := by
    simpa only [Pi.add_apply] using integral_add h1 h2
  rw [hpoly, hadd, hadd', integral_const_mul, integral_const_mul, integral_const_mul] at hnonneg
  change 0 ≤ B ^ 2 * A + (-2 * B * A) * B + A ^ 2 * C at hnonneg
  have hprod : 0 ≤ A * (A * C - B ^ 2) := by nlinarith [hnonneg]
  have hA' : 0 < A := hA
  have hdiff : 0 ≤ A * C - B ^ 2 := (mul_nonneg_iff_of_pos_left hA').mp hprod
  change B ^ 2 ≤ A * C
  linarith

/-! ## 8. Appendix B: kinetic model, differentiation, and asymptotics -/

namespace AppendixB

def occupation (χ ξ u : ℝ) : ℝ := (1 - Real.exp (ξ - u)) / (1 + χ * Real.exp (ξ - u))
def beta (κ u : ℝ) : ℝ := κ / (1 - κ * u)
def cutoff (κ u : ℝ) : ℝ := beta κ u * u
def sigma (q : ℝ) : ℝ := Real.sqrt (q * (q + 2))
def energyOccupation (κ χ u q : ℝ) : ℝ := occupation χ (q / beta κ u) u

def kineticConstant (mf c hp : ℝ) : ℝ := 8 * Real.pi * mf ^ 4 * c ^ 3 / hp ^ 3
def eta (mf c hp : ℝ) : ℝ := 8 * Real.pi * mf ^ 4 * c ^ 5 / (3 * hp ^ 3)

def momentA (κ χ u : ℝ) : ℝ :=
  ∫ q in (0 : ℝ)..cutoff κ u, energyOccupation κ χ u q * sigma q ^ 3

def momentB (κ χ u : ℝ) : ℝ :=
  ∫ q in (0 : ℝ)..cutoff κ u, energyOccupation κ χ u q * sigma q

def momentC (κ χ u : ℝ) : ℝ :=
  ∫ q in (0 : ℝ)..cutoff κ u, energyOccupation κ χ u q / sigma q

def densityEnergy (κ χ u mf c hp : ℝ) : ℝ :=
  kineticConstant mf c hp * (momentA κ χ u + momentB κ χ u)

def pressureEnergy (κ χ u mf c hp : ℝ) : ℝ :=
  kineticConstant mf c hp * c ^ 2 / 3 * momentA κ χ u

/-- The explicit density integral from slide 34, using ξ,u for the slide's x,y. -/
def densitySlide (κ χ u mf c hp : ℝ) : ℝ :=
  (8 * Real.sqrt 2 * Real.pi * c ^ 3 * mf ^ 4 * Real.rpow κ (3 / 2 : ℝ)) /
    (hp ^ 3 * Real.rpow (1 - κ * u) (3 / 2 : ℝ)) *
    (∫ ξ in (0 : ℝ)..u,
      Real.rpow ξ (1 / 2 : ℝ) * (1 + κ * ξ / (1 - κ * u)) ^ 2 *
      Real.rpow (1 + κ * ξ / (2 * (1 - κ * u))) (1 / 2 : ℝ) * occupation χ ξ u)

def pressureSlide (κ χ u mf c hp : ℝ) : ℝ :=
  eta mf c hp * Real.rpow (beta κ u) (5 / 2 : ℝ) *
    (∫ ξ in (0 : ℝ)..u,
      Real.rpow ξ (3 / 2 : ℝ) * Real.rpow (2 + beta κ u * ξ) (3 / 2 : ℝ) *
      occupation χ ξ u)

def rho0 (κ χ mf c hp : ℝ) : ℝ :=
  32 * Real.sqrt 2 * Real.pi * mf ^ 4 * c ^ 3 * Real.rpow κ (3 / 2 : ℝ) /
    (15 * hp ^ 3 * (1 + χ))

def pressure0 (κ χ mf c hp : ℝ) : ℝ :=
  64 * Real.sqrt 2 * Real.pi * mf ^ 4 * c ^ 5 * Real.rpow κ (5 / 2 : ℝ) /
    (105 * hp ^ 3 * (1 + χ))

def rhoInfinity (κ χ mf c hp : ℝ) : ℝ :=
  kineticConstant mf c hp * (∫ v in (0 : ℝ)..1,
    v ^ 3 * ((1 - Real.exp ((v - 1) / κ)) / (1 + χ * Real.exp ((v - 1) / κ))))

def enthalpy (κ u : ℝ) : ℝ := -Real.log (1 - κ * u)

theorem occupation_at_cutoff (χ u : ℝ) : occupation χ u u = 0 := by simp [occupation]

theorem beta_reciprocal (κ u : ℝ) (hκ : κ ≠ 0) (_hδ : 1 - κ * u ≠ 0) :
    1 / beta κ u + u = 1 / κ := by unfold beta; field_simp; ring

theorem hasDerivAt_enthalpy (κ u : ℝ) (_hδ : 1 - κ * u ≠ 0) :
    HasDerivAt (enthalpy κ) (beta κ u) u := by
  have ht : HasDerivAt (fun t : ℝ => 1 - κ * t) (-κ) u := by
    convert (hasDerivAt_const u 1).sub ((hasDerivAt_id u).const_mul κ) using 1 <;> first | rfl | ring
  convert (ht.log _hδ).neg using 1 <;> try rfl
  try simp only [enthalpy, beta]
  ring

/-- Transport-argument identity before differentiation of F. -/
theorem transport_argument (κ u q : ℝ) (hκ : κ ≠ 0) (_hδ : 1 - κ * u ≠ 0) :
    q / beta κ u - u = q / κ - (q + 1) * u := by
  unfold beta
  field_simp
  ring

/-! ## Kinetic differentiation: pointwise transport and fixed-domain kernels -/

def occupationSlope (χ z : ℝ) : ℝ :=
  (1 + χ) * Real.exp z / (1 + χ * Real.exp z) ^ 2

def occupationProfile (χ z : ℝ) : ℝ :=
  (1 - Real.exp z) / (1 + χ * Real.exp z)

theorem occupation_den_pos (χ z : ℝ) (hχ : 0 ≤ χ) :
    0 < 1 + χ * Real.exp z := by positivity

theorem hasDerivAt_occupationProfile (χ z : ℝ) (hχ : 0 ≤ χ) :
    HasDerivAt (occupationProfile χ) (-occupationSlope χ z) z := by
  have he := Real.hasDerivAt_exp z
  have hn := (hasDerivAt_const z 1).sub he
  have hd := (hasDerivAt_const z 1).add (he.const_mul χ)
  convert hn.div hd (ne_of_gt (occupation_den_pos χ z hχ)) using 1 <;> try rfl
  unfold occupationSlope
  simp only [Pi.add_apply, Pi.sub_apply]
  field_simp
  ring

theorem energyOccupation_affine (κ χ u q : ℝ) (hκ : κ ≠ 0) :
    energyOccupation κ χ u q = occupationProfile χ (q / κ - (q + 1) * u) := by
  unfold energyOccupation occupation occupationProfile beta
  have heq : q / (κ / (1 - κ * u)) - u = q / κ - (q + 1) * u := by
    field_simp
    ring
  rw [heq]

theorem hasDerivAt_energyOccupation_u (κ χ u q : ℝ) (hκ : κ ≠ 0) (hχ : 0 ≤ χ) :
    HasDerivAt (fun v => energyOccupation κ χ v q)
      ((q + 1) * occupationSlope χ (q / κ - (q + 1) * u)) u := by
  have ha : HasDerivAt (fun v : ℝ => q / κ - (q + 1) * v) (-(q + 1)) u := by
    convert (hasDerivAt_const u (q / κ)).sub ((hasDerivAt_id u).const_mul (q + 1)) using 1 <;> first | rfl | ring
  have hc := (hasDerivAt_occupationProfile χ _ hχ).comp u ha
  convert hc using 1 <;> try rfl
  · funext v; exact energyOccupation_affine κ χ v q hκ
  · ring

theorem hasDerivAt_energyOccupation_q (κ χ u q : ℝ) (hκ : κ ≠ 0) (hχ : 0 ≤ χ) :
    HasDerivAt (energyOccupation κ χ u)
      (-(1 / κ - u) * occupationSlope χ (q / κ - (q + 1) * u)) q := by
  have ha : HasDerivAt (fun p : ℝ => p / κ - (p + 1) * u) (1 / κ - u) q := by
    convert ((hasDerivAt_id q).div_const κ).sub
      (((hasDerivAt_id q).add_const 1).mul_const u) using 1 <;> first | rfl | ring
  have hc := (hasDerivAt_occupationProfile χ _ hχ).comp q ha
  convert hc using 1 <;> try rfl
  · funext p; exact energyOccupation_affine κ χ u p hκ
  · ring

/-- The transport identity for actual derivatives, not a postulated PDE. -/
theorem energyOccupation_transport (κ χ u q : ℝ)
    (hκ : κ ≠ 0) (hχ : 0 ≤ χ) (hδ : 1 - κ * u ≠ 0) :
    deriv (fun v => energyOccupation κ χ v q) u =
      -beta κ u * (q + 1) * deriv (energyOccupation κ χ u) q := by
  rw [(hasDerivAt_energyOccupation_u κ χ u q hκ hχ).deriv,
    (hasDerivAt_energyOccupation_q κ χ u q hκ hχ).deriv]
  unfold beta
  field_simp


def cutoffDeriv (κ u : ℝ) : ℝ := κ / (1 - κ * u) ^ 2

theorem hasDerivAt_beta (κ u : ℝ) (hδ : 1 - κ * u ≠ 0) :
    HasDerivAt (beta κ) (beta κ u ^ 2) u := by
  have hd : HasDerivAt (fun v : ℝ => 1 - κ * v) (-κ) u := by
    convert (hasDerivAt_const u 1).sub ((hasDerivAt_id u).const_mul κ) using 1 <;> first | rfl | ring
  convert (hasDerivAt_const u κ).div hd hδ using 1 <;> try rfl
  unfold beta
  field_simp
  ring

theorem hasDerivAt_cutoff (κ u : ℝ) (hδ : 1 - κ * u ≠ 0) :
    HasDerivAt (cutoff κ) (cutoffDeriv κ u) u := by
  convert (hasDerivAt_beta κ u hδ).mul (hasDerivAt_id u) using 1 <;> try rfl
  unfold beta cutoffDeriv
  simp only [id_eq]
  field_simp
  ring

theorem cutoff_pos (κ u : ℝ) (hκ : 0 < κ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    0 < cutoff κ u := mul_pos (div_pos hκ hδ) hu

theorem energyOccupation_at_cutoff (κ χ u : ℝ)
    (hκ : κ ≠ 0) (hδ : 1 - κ * u ≠ 0) :
    energyOccupation κ χ u (cutoff κ u) = 0 := by
  have hb : beta κ u ≠ 0 := div_ne_zero hκ hδ
  simp [energyOccupation, cutoff, mul_div_cancel_left₀ _ hb, occupation]

/-- Pullback occupation under q = cutoff(u)*t. -/
theorem energyOccupation_scaled (κ χ u t : ℝ)
    (hκ : κ ≠ 0) (hδ : 1 - κ * u ≠ 0) :
    energyOccupation κ χ u (cutoff κ u * t) = occupationProfile χ (u * (t - 1)) := by
  have hb : beta κ u ≠ 0 := div_ne_zero hκ hδ
  unfold energyOccupation occupation occupationProfile cutoff
  have ha : beta κ u * u * t / beta κ u - u = u * (t - 1) := by
    field_simp

  rw [ha]

def scaledOccupation (χ u t : ℝ) : ℝ := occupationProfile χ (u * (t - 1))
def scaledOccupationDeriv (χ u t : ℝ) : ℝ :=
  (1 - t) * occupationSlope χ (u * (t - 1))

theorem hasDerivAt_scaledOccupation (χ u t : ℝ) (hχ : 0 ≤ χ) :
    HasDerivAt (fun v => scaledOccupation χ v t) (scaledOccupationDeriv χ u t) u := by
  have hc := (hasDerivAt_occupationProfile χ _ hχ).comp u ((hasDerivAt_id u).mul_const (t - 1))
  dsimp at hc
  convert hc using 1 <;> try rfl
  unfold scaledOccupationDeriv
  ring

def shape (κ u t : ℝ) : ℝ := Real.sqrt (cutoff κ u) * Real.sqrt (cutoff κ u * t + 2)
def shapeDeriv (κ u t : ℝ) : ℝ :=
  cutoffDeriv κ u * (cutoff κ u * t + 1) /
    (Real.sqrt (cutoff κ u) * Real.sqrt (cutoff κ u * t + 2))

theorem sigma_scaled (L t : ℝ) (hL : 0 ≤ L) (ht : 0 ≤ t) :
    sigma (L * t) = Real.sqrt t * (Real.sqrt L * Real.sqrt (L * t + 2)) := by
  unfold sigma
  rw [Real.sqrt_mul (mul_nonneg hL ht), Real.sqrt_mul hL]
  ring

theorem hasDerivAt_shape (κ u t : ℝ) (hδ : 1 - κ * u ≠ 0)
    (hL : 0 < cutoff κ u) (ht : 0 ≤ t) :
    HasDerivAt (fun v => shape κ v t) (shapeDeriv κ u t) u := by
  have hp : 0 < cutoff κ u * t + 2 := by positivity
  have hsL : Real.sqrt (cutoff κ u) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL)
  have hsP : Real.sqrt (cutoff κ u * t + 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hd := hasDerivAt_cutoff κ u hδ
  have hc := (hd.sqrt (ne_of_gt hL)).mul
    ((hd.mul_const t).add_const 2 |>.sqrt (ne_of_gt hp))
  convert hc using 1 <;> try rfl
  unfold shapeDeriv
  have hs1 := Real.sq_sqrt hL.le
  have hs2 := Real.sq_sqrt hp.le
  have he : cutoffDeriv κ u / (2 * Real.sqrt (cutoff κ u)) * Real.sqrt (cutoff κ u * t + 2) +
      Real.sqrt (cutoff κ u) * (cutoffDeriv κ u * t / (2 * Real.sqrt (cutoff κ u * t + 2))) =
      cutoffDeriv κ u * ((Real.sqrt (cutoff κ u * t + 2)) ^ 2 +
        (Real.sqrt (cutoff κ u)) ^ 2 * t) /
        (2 * (Real.sqrt (cutoff κ u) * Real.sqrt (cutoff κ u * t + 2))) := by
    field_simp [hsL, hsP, two_ne_zero]
  rw [he, hs1, hs2]
  field_simp [hsL, hsP, two_ne_zero]
  ring

/-- Factorization isolates sqrt(t), independent of the differentiated parameter. -/
def scaledMomentKernel (n : ℕ) (κ χ u t : ℝ) : ℝ :=
  cutoff κ u * scaledOccupation χ u t * (Real.sqrt t * shape κ u t) ^ n

def scaledMomentKernelDeriv (n : ℕ) (κ χ u t : ℝ) : ℝ :=
  (cutoffDeriv κ u * scaledOccupation χ u t + cutoff κ u * scaledOccupationDeriv χ u t) *
    (Real.sqrt t * shape κ u t) ^ n +
  cutoff κ u * scaledOccupation χ u t *
    (n * (Real.sqrt t * shape κ u t) ^ (n - 1) * (Real.sqrt t * shapeDeriv κ u t))

theorem hasDerivAt_scaledMomentKernel (n : ℕ) (κ χ u t : ℝ)
    (hχ : 0 ≤ χ) (hδ : 1 - κ * u ≠ 0) (hL : 0 < cutoff κ u) (ht : 0 ≤ t) :
    HasDerivAt (fun v => scaledMomentKernel n κ χ v t)
      (scaledMomentKernelDeriv n κ χ u t) u := by
  exact ((hasDerivAt_cutoff κ u hδ).mul (hasDerivAt_scaledOccupation χ u t hχ)).mul
    (((hasDerivAt_shape κ u t hδ hL ht).const_mul (Real.sqrt t)).pow n)


def parameterRegion (κ : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < 1 - κ * p.1 ∧ 0 ≤ p.2}

theorem continuous_occupationProfile (χ : ℝ) (hχ : 0 ≤ χ) :
    Continuous (occupationProfile χ) := by
  exact (continuous_const.sub Real.continuous_exp).div
    (continuous_const.add (continuous_const.mul Real.continuous_exp))
    (fun z => ne_of_gt (occupation_den_pos χ z hχ))

theorem continuous_occupationSlope (χ : ℝ) (hχ : 0 ≤ χ) :
    Continuous (occupationSlope χ) := by
  exact (continuous_const.mul Real.continuous_exp).div
    ((continuous_const.add (continuous_const.mul Real.continuous_exp)).pow 2)
    (fun z => pow_ne_zero 2 (ne_of_gt (occupation_den_pos χ z hχ)))

theorem continuousOn_cutoff_fst (κ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => cutoff κ p.1) (parameterRegion κ) := by
  unfold cutoff beta
  exact (continuousOn_const.div
    (continuousOn_const.sub (continuousOn_const.mul continuous_fst.continuousOn))
    (fun p hp => ne_of_gt hp.2.1)).mul continuous_fst.continuousOn

theorem continuousOn_cutoffDeriv_fst (κ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => cutoffDeriv κ p.1) (parameterRegion κ) := by
  unfold cutoffDeriv
  exact continuousOn_const.div
    ((continuousOn_const.sub (continuousOn_const.mul continuous_fst.continuousOn)).pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt hp.2.1))

theorem continuousOn_shape (κ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => shape κ p.1 p.2) (parameterRegion κ) := by
  exact (continuousOn_cutoff_fst κ).sqrt.mul
    (((continuousOn_cutoff_fst κ).mul continuous_snd.continuousOn).add continuousOn_const).sqrt

theorem continuousOn_shapeDeriv (κ : ℝ) (hκ : 0 < κ) :
    ContinuousOn (fun p : ℝ × ℝ => shapeDeriv κ p.1 p.2) (parameterRegion κ) := by
  refine ((continuousOn_cutoffDeriv_fst κ).mul
    (((continuousOn_cutoff_fst κ).mul continuous_snd.continuousOn).add continuousOn_const)).div
      (continuousOn_shape κ) ?_
  intro p hp
  have hL := cutoff_pos κ p.1 hκ hp.1 hp.2.1
  have ht : 0 ≤ p.2 := hp.2.2
  exact mul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hL))
    (ne_of_gt (Real.sqrt_pos.2 (by positivity)))

theorem continuous_scaledOccupation (χ : ℝ) (hχ : 0 ≤ χ) :
    Continuous (fun p : ℝ × ℝ => scaledOccupation χ p.1 p.2) :=
  (continuous_occupationProfile χ hχ).comp
    (continuous_fst.mul (continuous_snd.sub continuous_const))

theorem continuous_scaledOccupationDeriv (χ : ℝ) (hχ : 0 ≤ χ) :
    Continuous (fun p : ℝ × ℝ => scaledOccupationDeriv χ p.1 p.2) :=
  (continuous_const.sub continuous_snd).mul
    ((continuous_occupationSlope χ hχ).comp
      (continuous_fst.mul (continuous_snd.sub continuous_const)))

theorem continuousOn_scaledMomentKernel (n : ℕ) (κ χ : ℝ) (hχ : 0 ≤ χ) :
    ContinuousOn (fun p : ℝ × ℝ => scaledMomentKernel n κ χ p.1 p.2) (parameterRegion κ) :=
  ((continuousOn_cutoff_fst κ).mul (continuous_scaledOccupation χ hχ).continuousOn).mul
    (((Real.continuous_sqrt.comp continuous_snd).continuousOn.mul (continuousOn_shape κ)).pow n)


theorem continuousOn_scaledMomentKernelDeriv (n : ℕ) (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    ContinuousOn (fun p : ℝ × ℝ => scaledMomentKernelDeriv n κ χ p.1 p.2) (parameterRegion κ) := by
  have hS : ContinuousOn (fun p : ℝ × ℝ => Real.sqrt p.2) (parameterRegion κ) :=
    (Real.continuous_sqrt.comp continuous_snd).continuousOn
  have hL := continuousOn_cutoff_fst κ
  have hLd := continuousOn_cutoffDeriv_fst κ
  have hF : ContinuousOn (fun p : ℝ × ℝ => scaledOccupation χ p.1 p.2) (parameterRegion κ) :=
    (continuous_scaledOccupation χ hχ).continuousOn
  have hFd : ContinuousOn (fun p : ℝ × ℝ => scaledOccupationDeriv χ p.1 p.2) (parameterRegion κ) :=
    (continuous_scaledOccupationDeriv χ hχ).continuousOn
  have hQ := continuousOn_shape κ
  have hQd := continuousOn_shapeDeriv κ hκ
  exact ((hLd.mul hF).add (hL.mul hFd)).mul ((hS.mul hQ).pow n) |>.add
    ((hL.mul hF).mul ((continuousOn_const.mul ((hS.mul hQ).pow (n - 1))).mul (hS.mul hQd)))

theorem exists_parameter_box (κ u : ℝ) (hκ : 0 < κ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ Icc (u - ε) (u + ε), 0 < v ∧ 0 < 1 - κ * v := by
  let ε : ℝ := min (u / 2) ((1 - κ * u) / (2 * κ))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨ε, hε, ?_⟩
  intro v hv
  have hεu : ε ≤ u / 2 := min_le_left _ _
  have hεδ : ε * (2 * κ) ≤ 1 - κ * u := by
    exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  constructor <;> nlinarith [hv.1, hv.2]

/-- A compact rectangle supplies domination automatically. This is the analytic
justification for differentiating the pulled-back integral; no derivative of an
integral is assumed. -/
theorem hasDerivAt_integral_unit_of_continuous (F D : ℝ → ℝ → ℝ) (u ε : ℝ)
    (hε : 0 < ε)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc (u - ε) (u + ε) ×ˢ Icc 0 1))
    (hD : ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) (Icc (u - ε) (u + ε) ×ˢ Icc 0 1))
    (hd : ∀ v ∈ Metric.ball u ε, ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun v => F v t) (D v t) v) :
    HasDerivAt (fun v => ∫ t in (0 : ℝ)..1, F v t) (∫ t in (0 : ℝ)..1, D u t) u := by
  have hvmem : ∀ v ∈ Metric.ball u ε, v ∈ Icc (u - ε) (u + ε) := by
    intro v hv
    rw [Metric.mem_ball, Real.dist_eq] at hv
    have ha := abs_lt.mp hv
    constructor <;> linarith
  have hvu : u ∈ Metric.ball u ε := Metric.mem_ball_self hε
  have hFc : ∀ v ∈ Metric.ball u ε, ContinuousOn (F v) (uIcc (0 : ℝ) 1) := by
    intro v hv
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hF.comp ((continuous_const : Continuous (fun _ : ℝ => v)).prodMk continuous_id).continuousOn
      (fun t ht => ⟨hvmem v hv, ht⟩)
  have hDc : ContinuousOn (D u) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hD.comp ((continuous_const : Continuous (fun _ : ℝ => u)).prodMk continuous_id).continuousOn
      (fun t ht => ⟨hvmem u hvu, ht⟩)
  have hc : IsCompact (Icc (u - ε) (u + ε) ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hD
  have hmeas : ∀ᶠ v in 𝓝 u,
      AEStronglyMeasurable (F v) (volume.restrict (uIoc (0 : ℝ) 1)) := by
    filter_upwards [Metric.ball_mem_nhds u hε] with v hv
    exact (hFc v hv).intervalIntegrable.def'.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      ∀ v ∈ Metric.ball u ε, ‖D v t‖ ≤ M := by
    filter_upwards [] with t
    intro ht v hv
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hM (v, t) ⟨hvmem v hv, ⟨ht.1.le, ht.2⟩⟩
  have hdiff : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → ∀ v ∈ Metric.ball u ε,
      HasDerivAt (fun v => F v t) (D v t) v := by
    filter_upwards [] with t
    intro ht v hv
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hd v hv t ⟨ht.1.le, ht.2⟩
  have hconst : IntervalIntegrable (fun _ : ℝ => M) volume 0 1 := intervalIntegrable_const
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (x₀ := u) (μ := volume) (a := (0 : ℝ)) (b := 1)
    (bound := fun _ => M) (Metric.ball_mem_nhds u hε) hmeas (hFc u hvu).intervalIntegrable
      hDc.intervalIntegrable.def'.aestronglyMeasurable hbound hconst hdiff).2


/-- All parameter dependence is now on a fixed, compact interval. -/
def sigmaMoment (n : ℕ) (κ χ u : ℝ) : ℝ :=
  ∫ q in (0 : ℝ)..cutoff κ u, energyOccupation κ χ u q * sigma q ^ n

theorem sigmaMoment_eq_scaled (n : ℕ) (κ χ u : ℝ)
    (hκ : 0 < κ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    sigmaMoment n κ χ u = ∫ t in (0 : ℝ)..1, scaledMomentKernel n κ χ u t := by
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun q => energyOccupation κ χ u q * sigma q ^ n) (cutoff κ u)
      (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at hs
  unfold sigmaMoment
  rw [← hs, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  dsimp only
  rw [energyOccupation_scaled κ χ u t (ne_of_gt hκ) (ne_of_gt hδ),
    sigma_scaled (cutoff κ u) t (cutoff_pos κ u hκ hu hδ).le ht.1]
  unfold scaledMomentKernel scaledOccupation shape
  ring

/-- Actual differentiation of the moving kinetic integral. Its derivative is the
integral of the explicitly computed pulled-back derivative. The hypotheses are
only the physical parameter inequalities, not integrability or differentiation
certificates. -/
theorem hasDerivAt_sigmaMoment_scaled (n : ℕ) (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    HasDerivAt (sigmaMoment n κ χ)
      (∫ t in (0 : ℝ)..1, scaledMomentKernelDeriv n κ χ u t) u := by
  obtain ⟨ε, hε, hbox⟩ := exists_parameter_box κ u hκ hu hδ
  have hsub : Icc (u - ε) (u + ε) ×ˢ Icc (0 : ℝ) 1 ⊆ parameterRegion κ := by
    intro p hp
    exact ⟨(hbox p.1 hp.1).1, (hbox p.1 hp.1).2, hp.2.1⟩
  have hvmem : ∀ v ∈ Metric.ball u ε, v ∈ Icc (u - ε) (u + ε) := by
    intro v hv
    rw [Metric.mem_ball, Real.dist_eq] at hv
    have ha := abs_lt.mp hv
    constructor <;> linarith
  have hd := hasDerivAt_integral_unit_of_continuous
    (scaledMomentKernel n κ χ) (scaledMomentKernelDeriv n κ χ) u ε hε
    ((continuousOn_scaledMomentKernel n κ χ hχ).mono hsub)
    ((continuousOn_scaledMomentKernelDeriv n κ χ hκ hχ).mono hsub)
    (fun v hv t ht => hasDerivAt_scaledMomentKernel n κ χ v t hχ
      (ne_of_gt (hbox v (hvmem v hv)).2)
      (cutoff_pos κ v hκ (hbox v (hvmem v hv)).1 (hbox v (hvmem v hv)).2) ht.1)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds u hε] with v hv
  exact sigmaMoment_eq_scaled n κ χ v hκ (hbox v (hvmem v hv)).1 (hbox v (hvmem v hv)).2


theorem continuous_energyOccupation (κ χ u : ℝ) (hκ : κ ≠ 0) (hχ : 0 ≤ χ) :
    Continuous (energyOccupation κ χ u) := by
  have hc : Continuous (fun q : ℝ => occupationProfile χ (q / κ - (q + 1) * u)) :=
    (continuous_occupationProfile χ hχ).comp
      ((continuous_id.div_const κ).sub ((continuous_id.add continuous_const).mul continuous_const))
  exact hc.congr (fun q => (energyOccupation_affine κ χ u q hκ).symm)

theorem continuous_sigma : Continuous sigma :=
  Real.continuous_sqrt.comp (continuous_id.mul (continuous_id.add continuous_const))

theorem sigma_pos (q : ℝ) (hq : 0 < q) : 0 < sigma q := by
  unfold sigma
  positivity

theorem sigma_sq (q : ℝ) (hq : 0 ≤ q) : sigma q ^ 2 = q * (q + 2) := by
  exact Real.sq_sqrt (mul_nonneg hq (by positivity))

theorem hasDerivAt_sigma (q : ℝ) (hq : 0 < q) :
    HasDerivAt sigma ((q + 1) / sigma q) q := by
  have hp := (hasDerivAt_id q).mul ((hasDerivAt_id q).add_const 2)
  dsimp at hp
  convert hp.sqrt (ne_of_gt (mul_pos hq (by positivity))) using 1 <;> try rfl
  simp only [Pi.mul_apply, id_eq]
  unfold sigma
  field_simp [ne_of_gt (sigma_pos q hq), two_ne_zero]
  ring

/-- The apparent singularity is integrable: it is q^(-1/2) times a continuous
factor. The endpoint q=0 is handled by the total real-valued definitions. -/
theorem intervalIntegrable_inv_sigma (L : ℝ) (hL : 0 ≤ L) :
    IntervalIntegrable (fun q => 1 / sigma q) volume 0 L := by
  have hc : ContinuousOn (fun q : ℝ => 1 / Real.sqrt (q + 2)) (uIcc 0 L) := by
    apply continuousOn_const.div (continuous_id.add continuous_const).sqrt.continuousOn
    intro q hq
    rw [uIcc_of_le hL] at hq
    have hqn : 0 ≤ q := hq.1
    change Real.sqrt (q + 2) ≠ 0
    exact ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := L)
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).mul_continuousOn hc
  apply hi.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with q hq
  rw [uIoc_of_le hL] at hq
  have hqn : 0 ≤ q := hq.1.le
  rw [Real.rpow_neg hqn, ← Real.sqrt_eq_rpow]
  unfold sigma
  rw [Real.sqrt_mul hqn]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

theorem intervalIntegrable_momentC (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    IntervalIntegrable (fun q => energyOccupation κ χ u q / sigma q) volume 0 (cutoff κ u) := by
  have hi := (intervalIntegrable_inv_sigma (cutoff κ u) (cutoff_pos κ u hκ hu hδ).le).continuousOn_mul (continuous_energyOccupation κ χ u (ne_of_gt hκ) hχ).continuousOn
  simpa only [one_div, div_eq_mul_inv, one_mul] using hi

/-- Momentum weights used by the transport integration by parts. -/
def transportWeight (n : ℕ) (q : ℝ) : ℝ := (q + 1) * sigma q ^ n

theorem hasDerivAt_transportWeight_three (q : ℝ) (hq : 0 < q) :
    HasDerivAt (transportWeight 3) (4 * sigma q ^ 3 + 3 * sigma q) q := by
  have hd := ((hasDerivAt_id q).add_const 1).mul ((hasDerivAt_sigma q hq).pow 3)
  convert hd using 1 <;> try rfl
  have hn : sigma q ≠ 0 := ne_of_gt (sigma_pos q hq)
  have he : sigma q ^ 3 + (q + 1) * (3 * sigma q ^ 2 * ((q + 1) / sigma q)) =
      sigma q ^ 3 + 3 * (q + 1) ^ 2 * sigma q := by
    field_simp [hn]

  simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, one_mul] at ⊢
  rw [he]
  have hs := sigma_sq q hq.le
  have hm := congrArg (fun v : ℝ => 3 * sigma q * v) hs
  try dsimp at hm
  nlinarith

theorem hasDerivAt_transportWeight_one (q : ℝ) (hq : 0 < q) :
    HasDerivAt (transportWeight 1) (2 * sigma q + 1 / sigma q) q := by
  have hd := ((hasDerivAt_id q).add_const 1).mul (hasDerivAt_sigma q hq)
  convert hd using 1 <;> try rfl
  · funext p; simp [transportWeight]
  · simp only [id_eq, one_mul]
    have hn : sigma q ≠ 0 := ne_of_gt (sigma_pos q hq)
    calc
      2 * sigma q + 1 / sigma q = (2 * sigma q ^ 2 + 1) / sigma q := by
        field_simp [hn]

      _ = (sigma q ^ 2 + (q + 1) ^ 2) / sigma q := by
        congr 1
        nlinarith [sigma_sq q hq.le]
      _ = sigma q + (q + 1) * ((q + 1) / sigma q) := by
        field_simp [hn]



theorem cutoffDeriv_identity (κ u : ℝ) (hδ : 1 - κ * u ≠ 0) :
    cutoffDeriv κ u * u = cutoff κ u * (1 + cutoff κ u) := by
  unfold cutoffDeriv cutoff beta
  field_simp [hδ]
  ring

theorem scaled_sigma_derivative_identity (κ u t : ℝ)
    (hL : 0 < cutoff κ u) (ht : 0 < t) :
    Real.sqrt t * shapeDeriv κ u t =
      cutoffDeriv κ u * t * (cutoff κ u * t + 1) / sigma (cutoff κ u * t) := by
  have hn : shape κ u t ≠ 0 := by
    unfold shape
    exact mul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hL))
      (ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  have htN : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  rw [sigma_scaled (cutoff κ u) t hL.le ht.le]
  change Real.sqrt t * (cutoffDeriv κ u * (cutoff κ u * t + 1) / shape κ u t) =
    cutoffDeriv κ u * t * (cutoff κ u * t + 1) / (Real.sqrt t * shape κ u t)
  field_simp [hn, htN]
  have hs := Real.sq_sqrt ht.le
  have hm := congrArg (fun v : ℝ => cutoffDeriv κ u * (cutoff κ u * t + 1) * shape κ u t * v) hs
  try dsimp at hm
  rw [hs]
  ring

def pulledBoundary (n : ℕ) (κ χ u t : ℝ) : ℝ :=
  t * scaledOccupation χ u t * sigma (cutoff κ u * t) ^ n

def pulledTransport (n : ℕ) (κ χ u t : ℝ) : ℝ :=
  cutoff κ u * (cutoff κ u * t + 1) * occupationSlope χ (u * (t - 1)) *
    sigma (cutoff κ u * t) ^ n

def pulledBoundaryDeriv (n : ℕ) (κ χ u t : ℝ) : ℝ :=
  (scaledMomentKernelDeriv n κ χ u t - pulledTransport n κ χ u t) / cutoffDeriv κ u

/-- The pulled endpoint contribution is a spatial derivative whose integral is zero. -/
theorem hasDerivAt_pulledBoundary (n : ℕ) (κ χ u t : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) (ht : 0 < t) :
    HasDerivAt (pulledBoundary n κ χ u) (pulledBoundaryDeriv n κ χ u t) t := by
  have hL := cutoff_pos κ u hκ hu hδ
  have hf : HasDerivAt (fun s => scaledOccupation χ u s)
      (-u * occupationSlope χ (u * (t - 1))) t := by
    have hc := (hasDerivAt_occupationProfile χ _ hχ).comp t
      (((hasDerivAt_id t).sub_const 1).const_mul u)
    dsimp at hc
    convert hc using 1 <;> try rfl
    ring
  have hs := (hasDerivAt_sigma (cutoff κ u * t) (mul_pos hL ht)).comp t
    ((hasDerivAt_id t).const_mul (cutoff κ u))
  have hd := ((hasDerivAt_id t).mul hf).mul (hs.pow n)
  dsimp at hd
  convert hd using 1 <;> try rfl
  have hN : cutoffDeriv κ u ≠ 0 := by unfold cutoffDeriv; positivity
  unfold pulledBoundaryDeriv pulledTransport scaledMomentKernelDeriv
  have hscl : sigma (cutoff κ u * t) = Real.sqrt t * shape κ u t :=
    sigma_scaled (cutoff κ u) t hL.le ht.le
  rw [← hscl,
    scaled_sigma_derivative_identity κ u t hL ht]
  unfold scaledOccupationDeriv
  apply (div_eq_iff hN).2
  simp only [div_eq_mul_inv, one_mul]
  have he := cutoffDeriv_identity κ u (ne_of_gt hδ)
  have hmult := congrArg (fun v : ℝ =>
    t * occupationSlope χ (u * (t - 1)) * sigma (cutoff κ u * t) ^ n * v) he
  try dsimp at hmult
  nlinarith only [hmult]


theorem continuous_pulledTransport (n : ℕ) (κ χ u : ℝ) (hχ : 0 ≤ χ) :
    Continuous (pulledTransport n κ χ u) := by
  exact (continuous_const.mul (continuous_const.mul continuous_id |>.add continuous_const)).mul
    ((continuous_occupationSlope χ hχ).comp
      (continuous_const.mul (continuous_id.sub continuous_const))) |>.mul
      ((continuous_sigma.comp (continuous_const.mul continuous_id)).pow n)

theorem continuous_pulledBoundary (n : ℕ) (κ χ u : ℝ) (hχ : 0 ≤ χ) :
    Continuous (pulledBoundary n κ χ u) := by
  have hf : Continuous (scaledOccupation χ u) :=
    (continuous_occupationProfile χ hχ).comp
      (continuous_const.mul (continuous_id.sub continuous_const))
  exact (continuous_id.mul hf).mul
    ((continuous_sigma.comp (continuous_const.mul continuous_id)).pow n)

theorem continuousOn_pulledBoundaryDeriv (n : ℕ) (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    ContinuousOn (pulledBoundaryDeriv n κ χ u) (Icc (0 : ℝ) 1) := by
  have hc : ContinuousOn (scaledMomentKernelDeriv n κ χ u) (Icc (0 : ℝ) 1) :=
    (continuousOn_scaledMomentKernelDeriv n κ χ hκ hχ).comp (f := fun t : ℝ => (u, t))
      ((continuous_const : Continuous (fun _ : ℝ => u)).prodMk continuous_id).continuousOn
      (fun t ht => ⟨hu, hδ, ht.1⟩)
  exact (hc.sub (continuous_pulledTransport n κ χ u hχ).continuousOn).div_const _

theorem integral_pulledBoundaryDeriv_zero (n : ℕ) (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    (∫ t in (0 : ℝ)..1, pulledBoundaryDeriv n κ χ u t) = 0 := by
  have hc := continuousOn_pulledBoundaryDeriv n κ χ u hκ hχ hu hδ
  have huIcc : ContinuousOn (pulledBoundaryDeriv n κ χ u) (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) (continuous_pulledBoundary n κ χ u hχ).continuousOn
    (fun t ht => hasDerivAt_pulledBoundary n κ χ u t hκ hχ hu hδ ht.1)
    huIcc.intervalIntegrable
  simpa [pulledBoundary, scaledOccupation, occupationProfile] using he

/-- The moving-endpoint term vanishes after the pullback; this is proved by FTC. -/
theorem integral_scaledMomentKernelDeriv_eq_transport (n : ℕ) (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    (∫ t in (0 : ℝ)..1, scaledMomentKernelDeriv n κ χ u t) =
      ∫ t in (0 : ℝ)..1, pulledTransport n κ χ u t := by
  have hc : ContinuousOn (scaledMomentKernelDeriv n κ χ u) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (continuousOn_scaledMomentKernelDeriv n κ χ hκ hχ).comp (f := fun t : ℝ => (u, t))
      ((continuous_const : Continuous (fun _ : ℝ => u)).prodMk continuous_id).continuousOn
      (fun t ht => ⟨hu, hδ, ht.1⟩)
  have hz := integral_pulledBoundaryDeriv_zero n κ χ u hκ hχ hu hδ
  unfold pulledBoundaryDeriv at hz
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub hc.intervalIntegrable
      ((continuous_pulledTransport n κ χ u hχ).intervalIntegrable (μ := volume) 0 1)] at hz
  have hn : cutoffDeriv κ u ≠ 0 := by unfold cutoffDeriv; positivity
  exact sub_eq_zero.mp ((div_eq_zero_iff).mp hz |>.resolve_right hn)

/-- Leibniz differentiation of the original q-integral, with zero cutoff term. -/
theorem hasDerivAt_sigmaMoment_transport (n : ℕ) (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    HasDerivAt (sigmaMoment n κ χ)
      (∫ q in (0 : ℝ)..cutoff κ u,
        (q + 1) * occupationSlope χ (q / κ - (q + 1) * u) * sigma q ^ n) u := by
  have hd := hasDerivAt_sigmaMoment_scaled n κ χ u hκ hχ hu hδ
  rw [integral_scaledMomentKernelDeriv_eq_transport n κ χ u hκ hχ hu hδ] at hd
  convert hd using 1 <;> try rfl
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun q => (q + 1) * occupationSlope χ (q / κ - (q + 1) * u) * sigma q ^ n)
    (cutoff κ u) (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at hs
  rw [← hs, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  have he : cutoff κ u * t / κ - (cutoff κ u * t + 1) * u = u * (t - 1) := by
    unfold cutoff beta
    field_simp [ne_of_gt hκ, ne_of_gt hδ]
    ring
  rw [he]
  unfold pulledTransport
  ring


def occupationQDeriv (κ χ u q : ℝ) : ℝ :=
  -(1 / κ - u) * occupationSlope χ (q / κ - (q + 1) * u)

theorem continuous_occupationQDeriv (κ χ u : ℝ) (hχ : 0 ≤ χ) :
    Continuous (occupationQDeriv κ χ u) :=
  continuous_const.mul ((continuous_occupationSlope χ hχ).comp
    ((continuous_id.div_const κ).sub ((continuous_id.add continuous_const).mul continuous_const)))

theorem continuous_transportWeight (n : ℕ) : Continuous (transportWeight n) :=
  (continuous_id.add continuous_const).mul (continuous_sigma.pow n)

/-- Generic transport integration by parts; the specific weight derivatives
and their integrability are proved above and instantiated below. -/
theorem kinetic_transport_by_parts (n : ℕ) (κ χ u : ℝ) (W' : ℝ → ℝ)
    (hn : 0 < n) (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u)
    (hW : ∀ q ∈ Ioo 0 (cutoff κ u), HasDerivAt (transportWeight n) (W' q) q)
    (hWi : IntervalIntegrable W' volume 0 (cutoff κ u)) :
    (∫ q in (0 : ℝ)..cutoff κ u,
      (q + 1) * occupationSlope χ (q / κ - (q + 1) * u) * sigma q ^ n) =
      beta κ u * ∫ q in (0 : ℝ)..cutoff κ u, energyOccupation κ χ u q * W' q := by
  have hL := cutoff_pos κ u hκ hu hδ
  have hf := continuous_energyOccupation κ χ u (ne_of_gt hκ) hχ
  have hfp := continuous_occupationQDeriv κ χ u hχ
  have hV := continuous_transportWeight n
  have hleft := (hfp.mul hV).intervalIntegrable (μ := volume) (0 : ℝ) (cutoff κ u)
  have hright := hWi.continuousOn_mul hf.continuousOn
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    hf.continuousOn hV.continuousOn
    (fun q _ => hasDerivAt_energyOccupation_q κ χ u q (ne_of_gt hκ) hχ)
    (fun q hq => hW q (by simpa only [min_eq_left hL.le, max_eq_right hL.le] using hq))
    (hfp.intervalIntegrable (μ := volume) 0 (cutoff κ u)) hWi
  have hsplit :
      (∫ q in (0 : ℝ)..cutoff κ u,
        occupationQDeriv κ χ u q * transportWeight n q + energyOccupation κ χ u q * W' q) =
      (∫ q in (0 : ℝ)..cutoff κ u, occupationQDeriv κ χ u q * transportWeight n q) +
      (∫ q in (0 : ℝ)..cutoff κ u, energyOccupation κ χ u q * W' q) := by
    convert intervalIntegral.integral_add hleft hright using 1 <;> rfl
  have hz :
      (∫ q in (0 : ℝ)..cutoff κ u, occupationQDeriv κ χ u q * transportWeight n q) +
      (∫ q in (0 : ℝ)..cutoff κ u, energyOccupation κ χ u q * W' q) = 0 := by
    change (∫ q in (0 : ℝ)..cutoff κ u,
      occupationQDeriv κ χ u q * transportWeight n q + energyOccupation κ χ u q * W' q) = _ at hparts
    rw [hsplit] at hparts
    simpa [energyOccupation_at_cutoff κ χ u (ne_of_gt hκ) (ne_of_gt hδ),
      transportWeight, sigma, zero_pow (Nat.ne_of_gt hn)] using hparts
  have he :
      (∫ q in (0 : ℝ)..cutoff κ u,
        (q + 1) * occupationSlope χ (q / κ - (q + 1) * u) * sigma q ^ n) =
      -beta κ u * ∫ q in (0 : ℝ)..cutoff κ u,
        occupationQDeriv κ χ u q * transportWeight n q := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro q _
    dsimp only
    unfold occupationQDeriv transportWeight beta
    field_simp [ne_of_gt hκ, ne_of_gt hδ]

  rw [he]
  have hs : (∫ q in (0 : ℝ)..cutoff κ u, occupationQDeriv κ χ u q * transportWeight n q) =
      -(∫ q in (0 : ℝ)..cutoff κ u, energyOccupation κ χ u q * W' q) := by linarith only [hz]
  rw [hs]
  ring

/-- Full A differentiation: only physical parameter inequalities are assumed. -/
theorem hasDerivAt_momentA (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    HasDerivAt (momentA κ χ)
      (beta κ u * (4 * momentA κ χ u + 3 * momentB κ χ u)) u := by
  have hd := hasDerivAt_sigmaMoment_transport 3 κ χ u hκ hχ hu hδ
  have hWi : IntervalIntegrable (fun q => 4 * sigma q ^ 3 + 3 * sigma q)
      volume 0 (cutoff κ u) :=
    ((continuous_const.mul (continuous_sigma.pow 3)).add
      (continuous_const.mul continuous_sigma)).intervalIntegrable (μ := volume) 0 (cutoff κ u)
  have hp := kinetic_transport_by_parts 3 κ χ u (fun q => 4 * sigma q ^ 3 + 3 * sigma q)
    (by norm_num) hκ hχ hu hδ (fun q hq => hasDerivAt_transportWeight_three q hq.1) hWi
  rw [hp] at hd
  convert hd using 1 <;> try rfl
  have hf := continuous_energyOccupation κ χ u (ne_of_gt hκ) hχ
  have hiA := (hf.mul (continuous_sigma.pow 3)).intervalIntegrable (μ := volume) (0 : ℝ) (cutoff κ u)
  have hiB := (hf.mul continuous_sigma).intervalIntegrable (μ := volume) (0 : ℝ) (cutoff κ u)
  have he : (fun q => energyOccupation κ χ u q * (4 * sigma q ^ 3 + 3 * sigma q)) =
      (fun q => 4 * (energyOccupation κ χ u q * sigma q ^ 3) +
        3 * (energyOccupation κ χ u q * sigma q)) := by funext q; ring
  change IntervalIntegrable (fun q => energyOccupation κ χ u q * sigma q ^ 3) volume 0 (cutoff κ u) at hiA
  change IntervalIntegrable (fun q => energyOccupation κ χ u q * sigma q) volume 0 (cutoff κ u) at hiB
  rw [he, intervalIntegral.integral_add (hiA.const_mul 4) (hiB.const_mul 3),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rfl

/-- Full B differentiation, including the integrable inverse-square-root kernel. -/
theorem hasDerivAt_momentB (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    HasDerivAt (momentB κ χ)
      (beta κ u * (2 * momentB κ χ u + momentC κ χ u)) u := by
  have hd := hasDerivAt_sigmaMoment_transport 1 κ χ u hκ hχ hu hδ
  have hWi : IntervalIntegrable (fun q => 2 * sigma q + 1 / sigma q)
      volume 0 (cutoff κ u) :=
    (continuous_const.mul continuous_sigma).intervalIntegrable (μ := volume) 0 (cutoff κ u) |>.add
      (intervalIntegrable_inv_sigma (cutoff κ u) (cutoff_pos κ u hκ hu hδ).le)
  have hp := kinetic_transport_by_parts 1 κ χ u (fun q => 2 * sigma q + 1 / sigma q)
    (by norm_num) hκ hχ hu hδ (fun q hq => hasDerivAt_transportWeight_one q hq.1) hWi
  rw [hp] at hd
  convert hd using 1 <;> try rfl
  · funext v; simp [sigmaMoment, momentB]
  · have hf := continuous_energyOccupation κ χ u (ne_of_gt hκ) hχ
    have hiB := (hf.mul continuous_sigma).intervalIntegrable (μ := volume) (0 : ℝ) (cutoff κ u)
    have hiC := intervalIntegrable_momentC κ χ u hκ hχ hu hδ
    have he : (fun q => energyOccupation κ χ u q * (2 * sigma q + 1 / sigma q)) =
        (fun q => 2 * (energyOccupation κ χ u q * sigma q) + energyOccupation κ χ u q / sigma q) := by
      funext q
      simp only [div_eq_mul_inv]
      ring
    change IntervalIntegrable (fun q => energyOccupation κ χ u q * sigma q) volume 0 (cutoff κ u) at hiB
    rw [he, intervalIntegral.integral_add (hiB.const_mul 2) hiC,
      intervalIntegral.integral_const_mul]
    rfl


/-- Pressure in mass-density units, Π = P/c². -/
def pressureMass (κ χ u mf c hp : ℝ) : ℝ :=
  kineticConstant mf c hp / 3 * momentA κ χ u

theorem pressureEnergy_div_c_sq (κ χ u mf c hp : ℝ) (hc : c ≠ 0) :
    pressureEnergy κ χ u mf c hp / c ^ 2 = pressureMass κ χ u mf c hp := by
  unfold pressureEnergy pressureMass
  field_simp [hc]


/-- The full EOS density derivative, now proved for the exact Appendix B integrals. -/
theorem hasDerivAt_densityEnergy (κ χ u mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    HasDerivAt (fun v => densityEnergy κ χ v mf c hp)
      (kineticConstant mf c hp * beta κ u *
        (4 * momentA κ χ u + 5 * momentB κ χ u + momentC κ χ u)) u := by
  have hd := ((hasDerivAt_momentA κ χ u hκ hχ hu hδ).add
    (hasDerivAt_momentB κ χ u hκ hχ hu hδ)).const_mul (kineticConstant mf c hp)
  convert hd using 1 <;> try rfl
  ring

/-- Π_u = Ckin β (4A/3+B). -/
theorem hasDerivAt_pressureMass (κ χ u mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    HasDerivAt (fun v => pressureMass κ χ v mf c hp)
      (kineticConstant mf c hp * beta κ u *
        (4 * momentA κ χ u / 3 + momentB κ χ u)) u := by
  have hd := (hasDerivAt_momentA κ χ u hκ hχ hu hδ).const_mul (kineticConstant mf c hp / 3)
  convert hd using 1 <;> try rfl
  ring

theorem hasDerivAt_pressureEnergy (κ χ u mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    HasDerivAt (fun v => pressureEnergy κ χ v mf c hp)
      (c ^ 2 * kineticConstant mf c hp * beta κ u *
        (4 * momentA κ χ u / 3 + momentB κ χ u)) u := by
  have hd := (hasDerivAt_pressureMass κ χ u mf c hp hκ hχ hu hδ).const_mul (c ^ 2)
  convert hd using 1 <;> try rfl
  · funext v
    unfold pressureEnergy pressureMass
    ring
  · ring

theorem energyOccupation_argument (κ u q : ℝ) (hκ : κ ≠ 0) (hδ : 1 - κ * u ≠ 0) :
    q / κ - (q + 1) * u = (q - cutoff κ u) * (1 - κ * u) / κ := by
  unfold cutoff beta
  field_simp [hκ, hδ]
  ring

theorem energyOccupation_nonneg (κ χ u q : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hδ : 0 < 1 - κ * u) (hq : q ≤ cutoff κ u) :
    0 ≤ energyOccupation κ χ u q := by
  rw [energyOccupation_affine κ χ u q (ne_of_gt hκ),
    energyOccupation_argument κ u q (ne_of_gt hκ) (ne_of_gt hδ)]
  unfold occupationProfile
  apply div_nonneg _ (occupation_den_pos χ _ hχ).le
  have hz : (q - cutoff κ u) * (1 - κ * u) / κ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq) hδ.le) hκ.le
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr hz)

theorem energyOccupation_pos (κ χ u q : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hδ : 0 < 1 - κ * u) (hq : q < cutoff κ u) :
    0 < energyOccupation κ χ u q := by
  rw [energyOccupation_affine κ χ u q (ne_of_gt hκ),
    energyOccupation_argument κ u q (ne_of_gt hκ) (ne_of_gt hδ)]
  unfold occupationProfile
  apply div_pos _ (occupation_den_pos χ _ hχ)
  have hz : (q - cutoff κ u) * (1 - κ * u) / κ < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr hq) hδ) hκ
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr hz)

theorem sigmaMoment_pos (n : ℕ) (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    0 < sigmaMoment n κ χ u := by
  have hL := cutoff_pos κ u hκ hu hδ
  apply intervalIntegral.integral_pos hL
    ((continuous_energyOccupation κ χ u (ne_of_gt hκ) hχ).mul (continuous_sigma.pow n)).continuousOn
  · intro q hq
    exact mul_nonneg (energyOccupation_nonneg κ χ u q hκ hχ hδ hq.2)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  · refine ⟨cutoff κ u / 2, ⟨(by positivity), (by linarith)⟩, ?_⟩
    exact mul_pos (energyOccupation_pos κ χ u _ hκ hχ hδ (by linarith))
      (pow_pos (sigma_pos _ (by positivity)) _)

theorem momentA_pos (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    0 < momentA κ χ u := sigmaMoment_pos 3 κ χ u hκ hχ hu hδ

theorem momentB_pos (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    0 < momentB κ χ u := by simpa [sigmaMoment, momentB] using sigmaMoment_pos 1 κ χ u hκ hχ hu hδ

theorem momentC_nonneg (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    0 ≤ momentC κ χ u := by
  apply intervalIntegral.integral_nonneg (cutoff_pos κ u hκ hu hδ).le
  intro q hq
  exact div_nonneg (energyOccupation_nonneg κ χ u q hκ hχ hδ hq.2) (Real.sqrt_nonneg _)

/-- The derivative ratio used in the dynamical system is the genuine EOS ratio. -/
theorem EOS_derivative_ratio (κ χ u mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u)
    (hK : kineticConstant mf c hp ≠ 0) :
    deriv (fun v => pressureMass κ χ v mf c hp) u /
      deriv (fun v => densityEnergy κ χ v mf c hp) u =
      (4 * momentA κ χ u / 3 + momentB κ χ u) /
        (4 * momentA κ χ u + 5 * momentB κ χ u + momentC κ χ u) := by
  rw [(hasDerivAt_pressureMass κ χ u mf c hp hκ hχ hu hδ).deriv,
    (hasDerivAt_densityEnergy κ χ u mf c hp hκ hχ hu hδ).deriv]
  have hb : beta κ u ≠ 0 := ne_of_gt (div_pos hκ hδ)
  have hA := momentA_pos κ χ u hκ hχ hu hδ
  have hB := momentB_pos κ χ u hκ hχ hu hδ
  have hC := momentC_nonneg κ χ u hκ hχ hu hδ
  have hden : 4 * momentA κ χ u + 5 * momentB κ χ u + momentC κ χ u ≠ 0 := by positivity
  field_simp [hK, hb, hden]



/-- Thermodynamic enthalpy identity for the exact kinetic EOS. -/
theorem pressureMass_derivative_enthalpy (κ χ u mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    deriv (fun v => pressureMass κ χ v mf c hp) u =
      beta κ u * (densityEnergy κ χ u mf c hp + pressureMass κ χ u mf c hp) := by
  rw [(hasDerivAt_pressureMass κ χ u mf c hp hκ hχ hu hδ).deriv]
  unfold densityEnergy pressureMass
  ring


/-- Cauchy--Schwarz for the actual cutoff kinetic moments. -/
theorem kinetic_moment_cauchySchwarz (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    momentB κ χ u ^ 2 ≤ momentA κ χ u * momentC κ χ u := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (cutoff κ u))
  let f : ℝ → ℝ := fun q => Real.sqrt (energyOccupation κ χ u q * sigma q ^ 3)
  let g : ℝ → ℝ := fun q => Real.sqrt (energyOccupation κ χ u q / sigma q)
  have hL := cutoff_pos κ u hκ hu hδ
  have hff : (fun q => f q ^ 2) =ᵐ[μ] (fun q => energyOccupation κ χ u q * sigma q ^ 3) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    exact Real.sq_sqrt (mul_nonneg (energyOccupation_nonneg κ χ u q hκ hχ hδ hq.2)
      (pow_nonneg (Real.sqrt_nonneg _) _))
  have hgg : (fun q => g q ^ 2) =ᵐ[μ] (fun q => energyOccupation κ χ u q / sigma q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    exact Real.sq_sqrt (div_nonneg (energyOccupation_nonneg κ χ u q hκ hχ hδ hq.2)
      (Real.sqrt_nonneg _))
  have hfg : (fun q => f q * g q) =ᵐ[μ] (fun q => energyOccupation κ χ u q * sigma q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    have hF := energyOccupation_nonneg κ χ u q hκ hχ hδ hq.2
    have hS := sigma_pos q hq.1
    change Real.sqrt (energyOccupation κ χ u q * sigma q ^ 3) *
      Real.sqrt (energyOccupation κ χ u q / sigma q) = _
    rw [← Real.sqrt_mul (mul_nonneg hF (pow_nonneg hS.le _))]
    have he : energyOccupation κ χ u q * sigma q ^ 3 * (energyOccupation κ χ u q / sigma q) =
        (energyOccupation κ χ u q * sigma q) ^ 2 := by
      field_simp [ne_of_gt hS]

    rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hF hS.le)]
  have hc := continuous_energyOccupation κ χ u (ne_of_gt hκ) hχ
  have hiA := (hc.mul (continuous_sigma.pow 3)).intervalIntegrable (μ := volume) 0 (cutoff κ u)
  have hiB := (hc.mul continuous_sigma).intervalIntegrable (μ := volume) 0 (cutoff κ u)
  have hiC := intervalIntegrable_momentC κ χ u hκ hχ hu hδ
  have hfint : Integrable (fun q => f q ^ 2) μ := hiA.1.congr hff.symm
  have hfgint : Integrable (fun q => f q * g q) μ := hiB.1.congr hfg.symm
  have hgint : Integrable (fun q => g q ^ 2) μ := hiC.1.congr hgg.symm
  have hAeq : (∫ q, f q ^ 2 ∂μ) = momentA κ χ u := by
    rw [integral_congr_ae hff]
    exact (intervalIntegral.integral_of_le hL.le).symm
  have hBeq : (∫ q, f q * g q ∂μ) = momentB κ χ u := by
    rw [integral_congr_ae hfg]
    exact (intervalIntegral.integral_of_le hL.le).symm
  have hCeq : (∫ q, g q ^ 2 ∂μ) = momentC κ χ u := by
    rw [integral_congr_ae hgg]
    exact (intervalIntegral.integral_of_le hL.le).symm
  have hApos : 0 < ∫ q, f q ^ 2 ∂μ := by rw [hAeq]; exact momentA_pos κ χ u hκ hχ hu hδ
  have hCS := RARTOV.integral_cauchy_schwarz μ f g hfint hfgint hgint hApos
  simpa only [hAeq, hBeq, hCeq] using hCS

/-- The admissible moments required by the barrier are now constructed from the
actual EOS, rather than assumed as an abstract family. -/
def kineticMoments (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) : RARTOV.Moments where
  A := momentA κ χ u
  B := momentB κ χ u
  C := momentC κ χ u
  A_pos := momentA_pos κ χ u hκ hχ hu hδ
  B_pos := momentB_pos κ χ u hκ hχ hu hδ
  C_nonneg := momentC_nonneg κ χ u hκ hχ hu hδ
  cauchySchwarz := kinetic_moment_cauchySchwarz κ χ u hκ hχ hu hδ


theorem EOS_derivative_ratio_eq_kineticMoments (κ χ u mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u)
    (hK : kineticConstant mf c hp ≠ 0) :
    deriv (fun v => pressureMass κ χ v mf c hp) u /
      deriv (fun v => densityEnergy κ χ v mf c hp) u =
      (kineticMoments κ χ u hκ hχ hu hδ).a :=
  EOS_derivative_ratio κ χ u mf c hp hκ hχ hu hδ hK

theorem EOS_w_ratio_eq_kineticMoments (κ χ u mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u)
    (hK : kineticConstant mf c hp ≠ 0) :
    pressureMass κ χ u mf c hp / densityEnergy κ χ u mf c hp =
      (kineticMoments κ χ u hκ hχ hu hδ).w := by
  have hAB : momentA κ χ u + momentB κ χ u ≠ 0 :=
    ne_of_gt (add_pos (momentA_pos κ χ u hκ hχ hu hδ) (momentB_pos κ χ u hκ hχ hu hδ))
  change (kineticConstant mf c hp / 3 * momentA κ χ u) /
    (kineticConstant mf c hp * (momentA κ χ u + momentB κ χ u)) =
    momentA κ χ u / (3 * (momentA κ χ u + momentB κ χ u))
  field_simp [hK, hAB]


theorem kineticConstant_pos (mf c hp : ℝ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    0 < kineticConstant mf c hp := by unfold kineticConstant; positivity

/-- The moment slope estimate is consequently an estimate for the actual EOS. -/
theorem EOS_slope_envelope (κ χ u mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u)
    (hK : kineticConstant mf c hp ≠ 0) :
    let w := pressureMass κ χ u mf c hp / densityEnergy κ χ u mf c hp
    deriv (fun v => pressureMass κ χ v mf c hp) u /
      deriv (fun v => densityEnergy κ χ v mf c hp) u ≤ 3 * w * (1 + w) / (1 + 9 * w) := by
  dsimp only
  rw [EOS_derivative_ratio_eq_kineticMoments κ χ u mf c hp hκ hχ hu hδ hK,
    EOS_w_ratio_eq_kineticMoments κ χ u mf c hp hκ hχ hu hδ hK]
  exact (kineticMoments κ χ u hκ hχ hu hδ).slope_envelope


/-- Comparator domination for the actual kinetic EOS and its actual derivatives. -/
theorem kinetic_EOS_field_domination (κ χ u mf c hp x y : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u)
    (hK : kineticConstant mf c hp ≠ 0)
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 ≤ y) (hwed : y ≤ 3 * x) :
    RARTOV.nonlinearField
      (pressureMass κ χ u mf c hp / densityEnergy κ χ u mf c hp)
      (deriv (fun v => pressureMass κ χ v mf c hp) u /
        deriv (fun v => densityEnergy κ χ v mf c hp) u) x y ≤
      RARTOV.linearField RARTOV.kStar x y := by
  rw [EOS_derivative_ratio_eq_kineticMoments κ χ u mf c hp hκ hχ hu hδ hK,
    EOS_w_ratio_eq_kineticMoments κ χ u mf c hp hκ hχ hu hδ hK]
  exact RARTOV.moments_field_domination (kineticMoments κ χ u hκ hχ hu hδ) x y hx hx1 hy hwed


set_option maxHeartbeats 500000
/-! ### Endpoint asymptotics of the actual kinetic integrals

Low endpoint: u tends to zero from above, with κ>0 and χ≥0.
High endpoint: u tends to 1/κ from below; δ=1−κu tends to zero from above.
Limits are proved from the integral kernels, rather than supplied as
hypotheses. `IsEquivalent` statements use Mathlib's standard relation.
The polytropic and radiation laws are along the parametric EOS; no existence
of a global inverse EOS or a TOV solution is assumed or concluded here.
-/

/-- Continuous extension of F(u(t-1))/u to u=0. -/
def lowOccupation (χ u t : ℝ) : ℝ :=
  (t - 1) * dslope (occupationProfile χ) 0 (u * (t - 1))

theorem continuous_lowOccupation (χ : ℝ) (hχ : 0 ≤ χ) :
    Continuous (fun p : ℝ × ℝ => lowOccupation χ p.1 p.2) := by
  have hds : Continuous (dslope (occupationProfile χ) 0) := by
    apply continuousOn_univ.mp
    exact (continuousOn_dslope (by simp : (univ : Set ℝ) ∈ 𝓝 (0 : ℝ))).mpr
      ⟨(continuous_occupationProfile χ hχ).continuousOn,
        (hasDerivAt_occupationProfile χ 0 hχ).differentiableAt⟩
  exact (continuous_snd.sub continuous_const).mul
    (hds.comp (continuous_fst.mul (continuous_snd.sub continuous_const)))

theorem occupationProfile_factor (χ u t : ℝ) :
    occupationProfile χ (u * (t - 1)) = u * lowOccupation χ u t := by
  have he := sub_smul_dslope (occupationProfile χ) 0 (u * (t - 1))
  simp only [sub_zero, smul_eq_mul] at he
  have hzero : occupationProfile χ 0 = 0 := by simp [occupationProfile]
  rw [hzero, sub_zero] at he
  unfold lowOccupation
  rw [← he]
  ring

theorem lowOccupation_at_zero (χ t : ℝ) (hχ : 0 ≤ χ) :
    lowOccupation χ 0 t = (1 - t) / (1 + χ) := by
  have hn : 1 + χ ≠ 0 := by positivity
  unfold lowOccupation
  rw [zero_mul, dslope_same, (hasDerivAt_occupationProfile χ 0 hχ).deriv]
  simp only [occupationSlope, Real.exp_zero, mul_one]
  field_simp [hn]
  ring

/-- A compact rectangle gives an integrable bound for a weighted parameter
integral, including the singular weight t^(-1/2). -/
theorem continuousAt_weighted_integral_unit (w : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hw : IntervalIntegrable w volume 0 1)
    (hc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc (-ε) ε ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousAt (fun u => ∫ t in (0 : ℝ)..1, w t * F u t) 0 := by
  have hvmem : ∀ v ∈ Metric.ball (0 : ℝ) ε, v ∈ Icc (-ε) ε := by
    intro v hv
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hv
    have ha := abs_lt.mp hv
    exact ⟨ha.1.le, ha.2.le⟩
  have hslice : ∀ v ∈ Metric.ball (0 : ℝ) ε, ContinuousOn (F v) (uIcc (0 : ℝ) 1) := by
    intro v hv
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hc.comp (f := fun t : ℝ => (v, t))
      ((continuous_const : Continuous (fun _ : ℝ => v)).prodMk continuous_id).continuousOn
      (fun t ht => ⟨hvmem v hv, ht⟩)
  have hk : IsCompact (Icc (-ε) ε ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hk.exists_bound_of_continuousOn hc
  have hmeas : ∀ᶠ v in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun t => w t * F v t)
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with v hv
    exact (hw.mul_continuousOn (hslice v hv)).def'.aestronglyMeasurable
  have hbound : ∀ᶠ v in 𝓝 (0 : ℝ), ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      ‖w t * F v t‖ ≤ ‖w t‖ * M := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with v hv
    exact Filter.Eventually.of_forall (fun t ht => by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hM (v, t) ⟨hvmem v hv, ⟨ht.1.le, ht.2⟩⟩) (norm_nonneg _))
  have hcont : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      ContinuousAt (fun v => w t * F v t) 0 := by
    filter_upwards [] with t
    intro ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hct : ContinuousOn (fun v => F v t) (Icc (-ε) ε) :=
      hc.comp (f := fun v : ℝ => (v, t))
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => t))).continuousOn
        (fun v hv => ⟨hv, ⟨ht.1.le, ht.2⟩⟩)
    exact continuousAt_const.mul (hct.continuousAt (Icc_mem_nhds (by linarith) hε))
  exact intervalIntegral.continuousAt_of_dominated_interval
    hmeas hbound (hw.norm.mul_const M) hcont

/-- Generic beta integral used to evaluate the three low-density coefficients. -/
theorem integral_rpow_one_sub (r : ℝ) (hr : -1 < r) :
    (∫ t in (0 : ℝ)..1, Real.rpow t r * (1 - t)) = 1 / ((r + 1) * (r + 2)) := by
  have hi := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) hr
  have hi' := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
    (show -1 < r + 1 by linarith)
  have he : (∫ t in (0 : ℝ)..1, Real.rpow t r * (1 - t)) =
      ∫ t in (0 : ℝ)..1, Real.rpow t r - Real.rpow t (r + 1) := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun t ht => by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      change t ^ r * (1 - t) = t ^ r - t ^ (r + 1)
      rw [Real.rpow_add ht.1, Real.rpow_one]
      ring)
  rw [he]
  change (∫ t in (0 : ℝ)..1, t ^ r - t ^ (r + 1)) = _
  rw [intervalIntegral.integral_sub hi hi',
    integral_rpow (Or.inl hr),
    integral_rpow (Or.inl (show -1 < r + 1 by linarith))]
  have h1 : r + 1 ≠ 0 := by linarith
  have h2 : r + 2 ≠ 0 := by linarith
  simp only [Real.one_rpow, Real.zero_rpow (ne_of_gt (show 0 < r + 1 by linarith)),
    Real.zero_rpow (ne_of_gt (show 0 < r + 1 + 1 by linarith)), sub_zero]
  rw [show r + 1 + 1 = r + 2 by ring]
  field_simp [h1, h2]
  ring

/-- Low-density natural normalization for the nth sigma moment. -/
def lowPower (n : ℕ) (u : ℝ) : ℝ := u ^ 2 * (Real.sqrt u) ^ n

def lowMomentFactor (n : ℕ) (κ χ u t : ℝ) : ℝ :=
  beta κ u * (Real.sqrt (beta κ u)) ^ n * lowOccupation χ u t *
    (Real.sqrt (beta κ u * u * t + 2)) ^ n

def lowMomentCoefficient (n : ℕ) (κ χ : ℝ) : ℝ :=
  κ * (Real.sqrt κ) ^ n * (Real.sqrt 2) ^ n / (1 + χ) *
    (∫ t in (0 : ℝ)..1, (Real.sqrt t) ^ n * (1 - t))

/-- The rescaling is an exact identity before taking a limit. -/
theorem sigmaMoment_low_ratio (n : ℕ) (κ χ u : ℝ)
    (hκ : 0 < κ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    sigmaMoment n κ χ u / lowPower n u =
      ∫ t in (0 : ℝ)..1, (Real.sqrt t) ^ n * lowMomentFactor n κ χ u t := by
  have hb : 0 < beta κ u := div_pos hκ hδ
  have hroot : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
  have hsig : ∀ t ∈ Icc (0 : ℝ) 1,
      sigma (cutoff κ u * t) = Real.sqrt u * Real.sqrt (beta κ u) * Real.sqrt t *
        Real.sqrt (beta κ u * u * t + 2) := by
    intro t ht
    unfold sigma cutoff
    rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hb.le hu.le) ht.1),
      Real.sqrt_mul (mul_nonneg hb.le hu.le), Real.sqrt_mul hb.le]
    ring
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun q => energyOccupation κ χ u q * sigma q ^ n) (cutoff κ u) (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at hs
  unfold sigmaMoment
  rw [← hs, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  dsimp only
  rw [energyOccupation_scaled κ χ u t (ne_of_gt hκ) (ne_of_gt hδ),
    occupationProfile_factor, hsig t ht]
  unfold cutoff lowPower lowMomentFactor
  field_simp [ne_of_gt hu, hroot]
  simp only [mul_pow]
  ring


theorem low_parameter_rectangle (κ : ℝ) (hκ : 0 < κ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ Icc (-ε) ε, 0 < 1 - κ * v := by
  let ε : ℝ := 1 / (2 * κ)
  have hε : 0 < ε := by positivity
  have he : κ * ε = 1 / 2 := by dsimp [ε]; field_simp <;> ring
  refine ⟨ε, hε, ?_⟩
  intro v hv
  have hm := mul_le_mul_of_nonneg_left hv.2 hκ.le
  rw [he] at hm
  linarith

theorem continuousOn_lowMomentFactor (n : ℕ) (κ χ ε : ℝ) (hχ : 0 ≤ χ)
    (hδ : ∀ v ∈ Icc (-ε) ε, 0 < 1 - κ * v) :
    ContinuousOn (fun p : ℝ × ℝ => lowMomentFactor n κ χ p.1 p.2)
      (Icc (-ε) ε ×ˢ Icc (0 : ℝ) 1) := by
  have hb : ContinuousOn (fun p : ℝ × ℝ => beta κ p.1) (Icc (-ε) ε ×ˢ Icc (0 : ℝ) 1) :=
    continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuous_fst.continuousOn))
      (fun p hp => ne_of_gt (hδ p.1 hp.1))
  exact ((hb.mul (hb.sqrt.pow n)).mul (continuous_lowOccupation χ hχ).continuousOn).mul
    ((((hb.mul continuous_fst.continuousOn).mul continuous_snd.continuousOn).add continuousOn_const).sqrt.pow n)

theorem integral_lowMomentFactor_at_zero (n : ℕ) (κ χ : ℝ) (hχ : 0 ≤ χ) :
    (∫ t in (0 : ℝ)..1, (Real.sqrt t) ^ n * lowMomentFactor n κ χ 0 t) =
      lowMomentCoefficient n κ χ := by
  have he : (fun t => (Real.sqrt t) ^ n * lowMomentFactor n κ χ 0 t) =
      (fun t => (κ * (Real.sqrt κ) ^ n * (Real.sqrt 2) ^ n / (1 + χ)) *
        ((Real.sqrt t) ^ n * (1 - t))) := by
    funext t
    unfold lowMomentFactor
    rw [lowOccupation_at_zero χ t hχ]
    simp only [beta, mul_zero, sub_zero, div_one, zero_mul, zero_add]
    ring
  rw [he, intervalIntegral.integral_const_mul]
  rfl

/-- Low-density moment limits with no assumed asymptotic or convergence certificates. -/
theorem tendsto_sigmaMoment_low (n : ℕ) (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun u => sigmaMoment n κ χ u / lowPower n u)
      (𝓝[>] (0 : ℝ)) (𝓝 (lowMomentCoefficient n κ χ)) := by
  obtain ⟨ε, hε, hδ⟩ := low_parameter_rectangle κ hκ
  have hw : IntervalIntegrable (fun t : ℝ => (Real.sqrt t) ^ n) volume 0 1 :=
    (Real.continuous_sqrt.pow n).intervalIntegrable 0 1
  have hc := continuousAt_weighted_integral_unit
    (fun t : ℝ => (Real.sqrt t) ^ n) (lowMomentFactor n κ χ) ε hε hw
      (continuousOn_lowMomentFactor n κ χ ε hχ hδ)
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [integral_lowMomentFactor_at_zero n κ χ hχ] at ht
  have he : (fun u => sigmaMoment n κ χ u / lowPower n u) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u => ∫ t in (0 : ℝ)..1, (Real.sqrt t) ^ n * lowMomentFactor n κ χ u t) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) hε),
      self_mem_nhdsWithin] with u hball hu
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hball
    have ha := abs_lt.mp hball
    exact sigmaMoment_low_ratio n κ χ u hκ hu (hδ u ⟨ha.1.le, ha.2.le⟩)
  exact (tendsto_congr' he).mpr ht

theorem lowPower_eq_rpow (n : ℕ) (u : ℝ) (hu : 0 < u) :
    lowPower n u = Real.rpow u ((n : ℝ) / 2 + 2) := by
  unfold lowPower
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hu.le]
  change u ^ 2 * u ^ ((1 / 2 : ℝ) * (n : ℝ)) = u ^ ((n : ℝ) / 2 + 2)
  rw [show (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) / 2 by ring,
    Real.rpow_add hu, Real.rpow_two]
  ring

def highParameter (κ δ : ℝ) : ℝ := (1 - δ) / κ

def highMomentFactor (n : ℕ) (κ χ δ t : ℝ) : ℝ :=
  (1 - δ) * occupationProfile χ (highParameter κ δ * (t - 1)) *
    (Real.sqrt ((1 - δ) * t * ((1 - δ) * t + 2 * δ))) ^ n

def highMomentCoefficient (n : ℕ) (κ χ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ n * occupationProfile χ ((t - 1) / κ)

theorem high_cutoff (κ δ : ℝ) (hκ : κ ≠ 0) (hδ : δ ≠ 0) :
    cutoff κ (highParameter κ δ) = (1 - δ) / δ := by
  unfold cutoff beta highParameter
  field_simp [hκ, hδ]
  ring

theorem high_sigma_scaled (κ δ t : ℝ) (hκ : κ ≠ 0) (hδ : 0 < δ) :
    δ * sigma (cutoff κ (highParameter κ δ) * t) =
      Real.sqrt ((1 - δ) * t * ((1 - δ) * t + 2 * δ)) := by
  rw [high_cutoff κ δ hκ (ne_of_gt hδ)]
  have he : δ ^ 2 * (((1 - δ) / δ * t) * ((1 - δ) / δ * t + 2)) =
      (1 - δ) * t * ((1 - δ) * t + 2 * δ) := by
    field_simp [ne_of_gt hδ]

  unfold sigma
  rw [← he, Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq_eq_abs, abs_of_pos hδ]

/-- Exact ultrarelativistic rescaling, using the original moving cutoff. -/
theorem sigmaMoment_high_scaled (n : ℕ) (κ χ δ : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    δ ^ (n + 1) * sigmaMoment n κ χ (highParameter κ δ) =
      ∫ t in (0 : ℝ)..1, highMomentFactor n κ χ δ t := by
  have hu : 0 < highParameter κ δ := div_pos (sub_pos.mpr hδ1) hκ
  have hden : 1 - κ * highParameter κ δ = δ := by unfold highParameter; field_simp <;> ring
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun q => energyOccupation κ χ (highParameter κ δ) q * sigma q ^ n)
    (cutoff κ (highParameter κ δ)) (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at hs
  unfold sigmaMoment
  rw [← hs, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [energyOccupation_scaled κ χ (highParameter κ δ) t (ne_of_gt hκ)
    (by rw [hden]; exact ne_of_gt hδ)]
  unfold highMomentFactor
  rw [← high_sigma_scaled κ δ t (ne_of_gt hκ) hδ,
    high_cutoff κ δ (ne_of_gt hκ) (ne_of_gt hδ), pow_succ, mul_pow]
  field_simp [ne_of_gt hδ]


theorem continuous_highMomentFactor (n : ℕ) (κ χ : ℝ) (hχ : 0 ≤ χ) :
    Continuous (fun p : ℝ × ℝ => highMomentFactor n κ χ p.1 p.2) := by
  have hu : Continuous (fun p : ℝ × ℝ => highParameter κ p.1) :=
    (continuous_const.sub continuous_fst).div_const κ
  have harg : Continuous (fun p : ℝ × ℝ => (1 - p.1) * p.2) :=
    (continuous_const.sub continuous_fst).mul continuous_snd
  exact ((continuous_const.sub continuous_fst).mul
    ((continuous_occupationProfile χ hχ).comp (hu.mul (continuous_snd.sub continuous_const)))).mul
      ((harg.mul (harg.add (continuous_const.mul continuous_fst))).sqrt.pow n)

theorem integral_highMomentFactor_at_zero (n : ℕ) (κ χ : ℝ) :
    (∫ t in (0 : ℝ)..1, highMomentFactor n κ χ 0 t) = highMomentCoefficient n κ χ := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  unfold highMomentFactor highParameter
  simp only [sub_zero, zero_mul, mul_zero, add_zero, one_mul]
  rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg ht.1]
  ring

theorem tendsto_sigmaMoment_high (n : ℕ) (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun δ => δ ^ (n + 1) * sigmaMoment n κ χ (highParameter κ δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (highMomentCoefficient n κ χ)) := by
  have hc := continuousAt_weighted_integral_unit (fun _ : ℝ => 1) (highMomentFactor n κ χ)
    1 (by norm_num) intervalIntegrable_const (continuous_highMomentFactor n κ χ hχ).continuousOn
  simp only [one_mul] at hc
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [integral_highMomentFactor_at_zero n κ χ] at ht
  have he : (fun δ => δ ^ (n + 1) * sigmaMoment n κ χ (highParameter κ δ)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ => ∫ t in (0 : ℝ)..1, highMomentFactor n κ χ δ t) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with δ hδ1 hδ
    exact sigmaMoment_high_scaled n κ χ δ hκ hδ hδ1
  exact (tendsto_congr' he).mpr ht


theorem integral_sqrt_pow_one_sub (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (Real.sqrt t) ^ n * (1 - t)) =
      1 / (((n : ℝ) / 2 + 1) * ((n : ℝ) / 2 + 2)) := by
  have he : (∫ t in (0 : ℝ)..1, (Real.sqrt t) ^ n * (1 - t)) =
      ∫ t in (0 : ℝ)..1, Real.rpow t ((n : ℝ) / 2) * (1 - t) := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun t ht => by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.1.le]
      congr 2
      ring)
  rw [he]
  exact integral_rpow_one_sub _ (by
    have hn : 0 ≤ (n : ℝ) := by positivity
    linarith)

def smallA (κ χ : ℝ) : ℝ := 8 * Real.sqrt 2 * κ ^ 2 * Real.sqrt κ / (35 * (1 + χ))
def smallB (κ χ : ℝ) : ℝ := 4 * Real.sqrt 2 * κ * Real.sqrt κ / (15 * (1 + χ))
def smallC (κ χ : ℝ) : ℝ := 4 * Real.sqrt κ / (3 * Real.sqrt 2 * (1 + χ))

theorem lowMomentCoefficient_one (κ χ : ℝ) (hχ : 0 ≤ χ) : lowMomentCoefficient 1 κ χ = smallB κ χ := by
  unfold lowMomentCoefficient smallB
  rw [integral_sqrt_pow_one_sub]
  norm_num
  have hn : 1 + χ ≠ 0 := by positivity
  field_simp [hn]


theorem lowMomentCoefficient_three (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    lowMomentCoefficient 3 κ χ = smallA κ χ := by
  unfold lowMomentCoefficient smallA
  rw [integral_sqrt_pow_one_sub]
  norm_num
  rw [pow_succ (Real.sqrt κ) 2, pow_succ (Real.sqrt 2) 2,
    Real.sq_sqrt hκ.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hn : 1 + χ ≠ 0 := by positivity
  field_simp [hn]
  ring

def lowCFactor (κ χ u t : ℝ) : ℝ :=
  Real.sqrt (beta κ u) * lowOccupation χ u t / Real.sqrt (beta κ u * u * t + 2)

theorem low_sqrt_argument_pos (κ u t : ℝ) (hδ : 0 < 1 - κ * u) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < beta κ u * u * t + 2 := by
  have he : beta κ u * u + 1 = 1 / (1 - κ * u) := by
    unfold beta
    field_simp <;> ring
  have hp : 0 < beta κ u * u + 1 := by rw [he]; positivity
  by_cases hs : 0 ≤ beta κ u * u
  · have ht0 := ht.1; positivity
  · have hn : beta κ u * u ≤ 0 := (lt_of_not_ge hs).le
    have hm := mul_le_mul_of_nonpos_left ht.2 hn
    simp only [mul_one] at hm
    linarith

theorem momentC_low_ratio (κ χ u : ℝ)
    (hκ : 0 < κ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    momentC κ χ u / (u * Real.sqrt u) =
      ∫ t in (0 : ℝ)..1, Real.rpow t (-(1 / 2 : ℝ)) * lowCFactor κ χ u t := by
  have hb : 0 < beta κ u := div_pos hκ hδ
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun q => energyOccupation κ χ u q / sigma q) (cutoff κ u) (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at hs
  unfold momentC
  rw [← hs, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall (fun t ht => by
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hsU : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
    have hsB : Real.sqrt (beta κ u) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
    have hsT : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht.1)
    have hsZ : Real.sqrt (beta κ u * u * t + 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (low_sqrt_argument_pos κ u t hδ ⟨ht.1.le, ht.2⟩))
    have hsig : sigma (cutoff κ u * t) = Real.sqrt u * Real.sqrt (beta κ u) * Real.sqrt t *
        Real.sqrt (beta κ u * u * t + 2) := by
      unfold sigma cutoff
      rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hb.le hu.le) ht.1.le),
        Real.sqrt_mul (mul_nonneg hb.le hu.le), Real.sqrt_mul hb.le]
      ring
    rw [energyOccupation_scaled κ χ u t (ne_of_gt hκ) (ne_of_gt hδ),
      occupationProfile_factor, hsig]
    change cutoff κ u * (u * lowOccupation χ u t /
      (Real.sqrt u * Real.sqrt (beta κ u) * Real.sqrt t * Real.sqrt (beta κ u * u * t + 2))) /
      (u * Real.sqrt u) = t ^ (-(1 / 2 : ℝ)) * lowCFactor κ χ u t
    rw [Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow]
    unfold cutoff lowCFactor
    field_simp [hsU, hsB, hsT, hsZ, ne_of_gt hu]
    ring_nf
    rw [Real.sq_sqrt hu.le, Real.sq_sqrt hb.le]
    ring)

theorem continuousOn_lowCFactor (κ χ ε : ℝ) (_hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hδ : ∀ v ∈ Icc (-ε) ε, 0 < 1 - κ * v) :
    ContinuousOn (fun p : ℝ × ℝ => lowCFactor κ χ p.1 p.2)
      (Icc (-ε) ε ×ˢ Icc (0 : ℝ) 1) := by
  have hb : ContinuousOn (fun p : ℝ × ℝ => beta κ p.1) (Icc (-ε) ε ×ˢ Icc (0 : ℝ) 1) :=
    continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuous_fst.continuousOn))
      (fun p hp => ne_of_gt (hδ p.1 hp.1))
  exact (hb.sqrt.mul (continuous_lowOccupation χ hχ).continuousOn).div
    ((((hb.mul continuous_fst.continuousOn).mul continuous_snd.continuousOn).add continuousOn_const).sqrt)
    (fun p hp => ne_of_gt (Real.sqrt_pos.2
      (low_sqrt_argument_pos κ p.1 p.2 (hδ p.1 hp.1) hp.2)))

/-- The singular moment has a rigorous weighted dominated-convergence limit. -/
theorem tendsto_momentC_low (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun u => momentC κ χ u / (u * Real.sqrt u)) (𝓝[>] (0 : ℝ)) (𝓝 (smallC κ χ)) := by
  obtain ⟨ε, hε, hδ⟩ := low_parameter_rectangle κ hκ
  have hw := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))
  have hc := continuousAt_weighted_integral_unit
    (fun t => Real.rpow t (-(1 / 2 : ℝ))) (lowCFactor κ χ) ε hε hw
    (continuousOn_lowCFactor κ χ ε hκ hχ hδ)
  have hlimit : (∫ t in (0 : ℝ)..1, Real.rpow t (-(1 / 2 : ℝ)) * lowCFactor κ χ 0 t) = smallC κ χ := by
    have he : (fun t => Real.rpow t (-(1 / 2 : ℝ)) * lowCFactor κ χ 0 t) =
        (fun t => (Real.sqrt κ / (Real.sqrt 2 * (1 + χ))) *
          (Real.rpow t (-(1 / 2 : ℝ)) * (1 - t))) := by
      funext t
      unfold lowCFactor
      rw [lowOccupation_at_zero χ t hχ]
      simp only [beta, mul_zero, sub_zero, div_one, zero_mul, zero_add]
      have hn : 1 + χ ≠ 0 := by positivity
      have h2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
      field_simp [hn, h2]

    rw [he, intervalIntegral.integral_const_mul, integral_rpow_one_sub _ (by norm_num)]
    norm_num
    unfold smallC
    have hn : 1 + χ ≠ 0 := by positivity
    have h2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
    field_simp [hn, h2]

  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [hlimit] at ht
  have he : (fun u => momentC κ χ u / (u * Real.sqrt u)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u => ∫ t in (0 : ℝ)..1, Real.rpow t (-(1 / 2 : ℝ)) * lowCFactor κ χ u t) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) hε),
      self_mem_nhdsWithin] with u hball hu
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hball
    have ha := abs_lt.mp hball
    exact momentC_low_ratio κ χ u hκ hu (hδ u ⟨ha.1.le, ha.2.le⟩)
  exact (tendsto_congr' he).mpr ht


theorem tendsto_momentA_low (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun u => momentA κ χ u / lowPower 3 u) (𝓝[>] (0 : ℝ)) (𝓝 (smallA κ χ)) := by
  simpa only [sigmaMoment, momentA, lowMomentCoefficient_three κ χ hκ hχ] using tendsto_sigmaMoment_low 3 κ χ hκ hχ

theorem tendsto_momentB_low (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun u => momentB κ χ u / lowPower 1 u) (𝓝[>] (0 : ℝ)) (𝓝 (smallB κ χ)) := by
  simpa only [sigmaMoment, momentB, pow_one, lowMomentCoefficient_one κ χ hχ] using
    tendsto_sigmaMoment_low 1 κ χ hκ hχ

theorem lowPower_three_eq (u : ℝ) (hu : 0 < u) : lowPower 3 u = u * lowPower 1 u := by
  unfold lowPower
  rw [pow_succ (Real.sqrt u) 2, Real.sq_sqrt hu.le, pow_one]
  ring

theorem lowPower_one_pos (u : ℝ) (hu : 0 < u) : 0 < lowPower 1 u := by
  unfold lowPower
  positivity

theorem lowPower_three_pos (u : ℝ) (hu : 0 < u) : 0 < lowPower 3 u := by
  unfold lowPower
  positivity

theorem rho0_eq (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) (hhp : hp ≠ 0) :
    rho0 κ χ mf c hp = kineticConstant mf c hp * smallB κ χ := by
  have he : (3 / 2 : ℝ) = 1 + 1 / 2 := by ring
  unfold rho0 kineticConstant smallB
  change 32 * Real.sqrt 2 * Real.pi * mf ^ 4 * c ^ 3 * κ ^ (3 / 2 : ℝ) /
    (15 * hp ^ 3 * (1 + χ)) = _
  rw [he, Real.rpow_add hκ, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hn : 1 + χ ≠ 0 := by positivity
  field_simp [hhp, hn]
  ring

theorem pressure0_eq (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) (hhp : hp ≠ 0) :
    pressure0 κ χ mf c hp = kineticConstant mf c hp * c ^ 2 / 3 * smallA κ χ := by
  have he : (5 / 2 : ℝ) = 2 + 1 / 2 := by ring
  unfold pressure0 kineticConstant smallA
  change 64 * Real.sqrt 2 * Real.pi * mf ^ 4 * c ^ 5 * κ ^ (5 / 2 : ℝ) /
    (105 * hp ^ 3 * (1 + χ)) = _
  rw [he, Real.rpow_add hκ, Real.rpow_two, ← Real.sqrt_eq_rpow]
  have hn : 1 + χ ≠ 0 := by positivity
  field_simp [hhp, hn]
  ring

/-- The exact low-density coefficient ρ₀, with the manuscript's u^(5/2) normalization. -/
theorem tendsto_densityEnergy_low (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hhp : hp ≠ 0) :
    Tendsto (fun u => densityEnergy κ χ u mf c hp / Real.rpow u (5 / 2 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (rho0 κ χ mf c hp)) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht := ((hu.mul (tendsto_momentA_low κ χ hκ hχ)).add
    (tendsto_momentB_low κ χ hκ hχ)).const_mul (kineticConstant mf c hp)
  have he : (fun u => densityEnergy κ χ u mf c hp / Real.rpow u (5 / 2 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u => kineticConstant mf c hp *
        (u * (momentA κ χ u / lowPower 3 u) + momentB κ χ u / lowPower 1 u)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hn : lowPower 1 u ≠ 0 := ne_of_gt (lowPower_one_pos u hu)
    have hp : lowPower 1 u = Real.rpow u (5 / 2 : ℝ) := by
      convert lowPower_eq_rpow 1 u hu using 1; norm_num
    unfold densityEnergy
    rw [← hp, lowPower_three_eq u hu]
    have hup : 0 < u := hu
    field_simp [hn, ne_of_gt hup]

  apply (tendsto_congr' he).mpr
  simpa only [zero_mul, zero_add, ← rho0_eq κ χ mf c hp hκ hχ hhp] using ht

/-- The exact low-density pressure coefficient P₀. -/
theorem tendsto_pressureEnergy_low (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hhp : hp ≠ 0) :
    Tendsto (fun u => pressureEnergy κ χ u mf c hp / Real.rpow u (7 / 2 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (pressure0 κ χ mf c hp)) := by
  have ht := (tendsto_momentA_low κ χ hκ hχ).const_mul (kineticConstant mf c hp * c ^ 2 / 3)
  have he : (fun u => pressureEnergy κ χ u mf c hp / Real.rpow u (7 / 2 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u => kineticConstant mf c hp * c ^ 2 / 3 * (momentA κ χ u / lowPower 3 u)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hp : lowPower 3 u = Real.rpow u (7 / 2 : ℝ) := by
      convert lowPower_eq_rpow 3 u hu using 1; norm_num
    unfold pressureEnergy
    rw [← hp]
    ring
  apply (tendsto_congr' he).mpr
  simpa only [pressure0_eq κ χ mf c hp hκ hχ hhp] using ht


theorem occupationProfile_nonneg (χ z : ℝ) (hχ : 0 ≤ χ) (hz : z ≤ 0) :
    0 ≤ occupationProfile χ z :=
  div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr hz)) (occupation_den_pos χ z hχ).le

theorem occupationProfile_pos (χ z : ℝ) (hχ : 0 ≤ χ) (hz : z < 0) :
    0 < occupationProfile χ z :=
  div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr hz)) (occupation_den_pos χ z hχ)

theorem highMomentCoefficient_pos (n : ℕ) (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    0 < highMomentCoefficient n κ χ := by
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
    ((continuous_id.pow n).mul ((continuous_occupationProfile χ hχ).comp
      ((continuous_id.sub continuous_const).div_const κ))).continuousOn
  · intro t ht
    exact mul_nonneg (pow_nonneg ht.1.le _) (occupationProfile_nonneg χ _ hχ
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht.2) hκ.le))
  · refine ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩, ?_⟩
    exact mul_pos (pow_pos (by norm_num) _) (occupationProfile_pos χ _ hχ
      (div_neg_of_neg_of_pos (by norm_num) hκ))

theorem rhoInfinity_eq (κ χ mf c hp : ℝ) :
    rhoInfinity κ χ mf c hp = kineticConstant mf c hp * highMomentCoefficient 3 κ χ := rfl

/-- The relativistic endpoint coefficient δ⁴ρ -> ρ∞. -/
theorem tendsto_densityEnergy_high (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun δ => δ ^ 4 * densityEnergy κ χ (highParameter κ δ) mf c hp)
      (𝓝[>] (0 : ℝ)) (𝓝 (rhoInfinity κ χ mf c hp)) := by
  have hu : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun δ => δ ^ 4 * momentA κ χ (highParameter κ δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (highMomentCoefficient 3 κ χ)) :=
    tendsto_sigmaMoment_high 3 κ χ hκ hχ
  have hB : Tendsto (fun δ => δ ^ 2 * momentB κ χ (highParameter κ δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (highMomentCoefficient 1 κ χ)) := by
    simpa only [sigmaMoment, momentB, pow_one] using tendsto_sigmaMoment_high 1 κ χ hκ hχ
  have ht := (hA.add ((hu.pow 2).mul hB)).const_mul (kineticConstant mf c hp)
  have he : (fun δ => δ ^ 4 * densityEnergy κ χ (highParameter κ δ) mf c hp) =
      (fun δ => kineticConstant mf c hp * (δ ^ 4 * momentA κ χ (highParameter κ δ) +
        δ ^ 2 * (δ ^ 2 * momentB κ χ (highParameter κ δ)))) := by
    funext δ
    unfold densityEnergy
    ring
  rw [he]
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, add_zero, ← rhoInfinity_eq] using ht

/-- The common relativistic pressure coefficient. -/
theorem tendsto_pressureEnergy_high (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun δ => δ ^ 4 * pressureEnergy κ χ (highParameter κ δ) mf c hp)
      (𝓝[>] (0 : ℝ)) (𝓝 (c ^ 2 * rhoInfinity κ χ mf c hp / 3)) := by
  have ht := (tendsto_sigmaMoment_high 3 κ χ hκ hχ).const_mul
    (kineticConstant mf c hp * c ^ 2 / 3)
  have he : (fun δ => δ ^ 4 * pressureEnergy κ χ (highParameter κ δ) mf c hp) =
      (fun δ => kineticConstant mf c hp * c ^ 2 / 3 *
        (δ ^ 4 * momentA κ χ (highParameter κ δ))) := by
    funext δ
    unfold pressureEnergy
    ring
  rw [he]
  convert ht using 1 <;> try rfl
  rw [rhoInfinity_eq]
  ring

/-- Reparametrization from u ↑ 1/κ to δ ↓ 0. -/
theorem tendsto_delta_endpoint (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun u => 1 - κ * u) (𝓝[<] (1 / κ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun u : ℝ => 1 - κ * u) :=
      continuous_const.sub (continuous_const.mul continuous_id)
    have ht := hc.tendsto (1 / κ)
    have he : 1 - κ * (1 / κ) = 0 := by field_simp <;> ring
    rw [he] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    have hm : κ * u < 1 := by
      have hh := mul_lt_mul_of_pos_left hu hκ
      simpa only [mul_one_div_cancel (ne_of_gt hκ)] using hh
    exact sub_pos.mpr hm

theorem highParameter_delta (κ u : ℝ) (hκ : κ ≠ 0) : highParameter κ (1 - κ * u) = u := by
  unfold highParameter
  field_simp <;> ring

theorem tendsto_densityEnergy_relativistic (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun u => (1 - κ * u) ^ 4 * densityEnergy κ χ u mf c hp)
      (𝓝[<] (1 / κ)) (𝓝 (rhoInfinity κ χ mf c hp)) := by
  have ht := (tendsto_densityEnergy_high κ χ mf c hp hκ hχ).comp (tendsto_delta_endpoint κ hκ)
  dsimp only [Function.comp_def] at ht
  simpa only [highParameter_delta κ _ (ne_of_gt hκ)] using ht

theorem tendsto_pressureEnergy_relativistic (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun u => (1 - κ * u) ^ 4 * pressureEnergy κ χ u mf c hp)
      (𝓝[<] (1 / κ)) (𝓝 (c ^ 2 * rhoInfinity κ χ mf c hp / 3)) := by
  have ht := (tendsto_pressureEnergy_high κ χ mf c hp hκ hχ).comp (tendsto_delta_endpoint κ hκ)
  dsimp only [Function.comp_def] at ht
  simpa only [highParameter_delta κ _ (ne_of_gt hκ)] using ht


def kineticW (κ χ u : ℝ) : ℝ := momentA κ χ u / (3 * (momentA κ χ u + momentB κ χ u))
def kineticSlope (κ χ u : ℝ) : ℝ :=
  (4 * momentA κ χ u / 3 + momentB κ χ u) /
    (4 * momentA κ χ u + 5 * momentB κ χ u + momentC κ χ u)

theorem eventually_low_parameters (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < u ∧ 0 < 1 - κ * u := by
  obtain ⟨ε, hε, hδ⟩ := low_parameter_rectangle κ hκ
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) hε),
    self_mem_nhdsWithin] with u hball hu
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hball
  have ha := abs_lt.mp hball
  exact ⟨hu, hδ u ⟨ha.1.le, ha.2.le⟩⟩

theorem kineticW_low_identity (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    kineticW κ χ u / u = (momentA κ χ u / lowPower 3 u) /
      (3 * (u * (momentA κ χ u / lowPower 3 u) + momentB κ χ u / lowPower 1 u)) := by
  have hA := momentA_pos κ χ u hκ hχ hu hδ
  have hB := momentB_pos κ χ u hκ hχ hu hδ
  have hP := lowPower_one_pos u hu
  have hP3 := lowPower_three_pos u hu
  have hN : 3 * (u * (momentA κ χ u / lowPower 3 u) + momentB κ χ u / lowPower 1 u) ≠ 0 := by positivity
  have hAB : momentA κ χ u + momentB κ χ u ≠ 0 := by positivity
  unfold kineticW
  field_simp [hN, ne_of_gt hu, ne_of_gt hP, ne_of_gt hP3, hAB]
  rw [lowPower_three_eq u hu]
  ring

theorem smallA_div_smallB (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    smallA κ χ / (3 * smallB κ χ) = 2 * κ / 7 := by
  have hχn : 1 + χ ≠ 0 := by positivity
  have hκn : Real.sqrt κ ≠ 0 := by positivity
  have h2n : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  unfold smallA smallB
  field_simp [hχn, hκn, h2n, ne_of_gt hκ]
  ring

/-- w ~ (2κ/7)u at vacuum, with its coefficient proved from the moments. -/
theorem tendsto_kineticW_over_u (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun u => kineticW κ χ u / u) (𝓝[>] (0 : ℝ)) (𝓝 (2 * κ / 7)) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hA := tendsto_momentA_low κ χ hκ hχ
  have hB := tendsto_momentB_low κ χ hκ hχ
  have hbn : 3 * (0 * smallA κ χ + smallB κ χ) ≠ 0 := by simp only [zero_mul, zero_add]; unfold smallB; positivity
  have ht := hA.div (((hu.mul hA).add hB).const_mul 3) hbn
  have he : (fun u => kineticW κ χ u / u) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u => (momentA κ χ u / lowPower 3 u) /
        (3 * (u * (momentA κ χ u / lowPower 3 u) + momentB κ χ u / lowPower 1 u))) := by
    filter_upwards [eventually_low_parameters κ hκ] with u hp
    exact kineticW_low_identity κ χ u hκ hχ hp.1 hp.2
  apply (tendsto_congr' he).mpr
  convert ht using 1 <;> first | rfl | simp only [zero_mul, zero_add, smallA_div_smallB κ χ hκ hχ]

theorem lowPower_three_eq_base (u : ℝ) (hu : 0 < u) : lowPower 3 u = u ^ 2 * (u * Real.sqrt u) := by
  rw [lowPower_three_eq u hu]
  unfold lowPower
  simp only [pow_one]
  ring

theorem kineticSlope_low_identity (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    kineticSlope κ χ u / u =
      (4 * u * (momentA κ χ u / lowPower 3 u) / 3 + momentB κ χ u / lowPower 1 u) /
      (4 * u ^ 2 * (momentA κ χ u / lowPower 3 u) +
        5 * u * (momentB κ χ u / lowPower 1 u) + momentC κ χ u / (u * Real.sqrt u)) := by
  have hA := momentA_pos κ χ u hκ hχ hu hδ
  have hB := momentB_pos κ χ u hκ hχ hu hδ
  have hC := momentC_nonneg κ χ u hκ hχ hu hδ
  have hP := lowPower_one_pos u hu
  have hP3 := lowPower_three_pos u hu
  have hS : 0 < u * Real.sqrt u := by positivity
  have hN : 4 * u ^ 2 * (momentA κ χ u / lowPower 3 u) +
      5 * u * (momentB κ χ u / lowPower 1 u) + momentC κ χ u / (u * Real.sqrt u) ≠ 0 := by positivity
  have hD : 4 * momentA κ χ u + 5 * momentB κ χ u + momentC κ χ u ≠ 0 := by positivity
  unfold kineticSlope
  field_simp [hN, ne_of_gt hu, ne_of_gt hP, ne_of_gt hP3, ne_of_gt hS, hD]
  rw [lowPower_three_eq_base u hu]
  unfold lowPower
  simp only [pow_one]
  ring

theorem smallB_div_smallC (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    smallB κ χ / smallC κ χ = 2 * κ / 5 := by
  have hχn : 1 + χ ≠ 0 := by positivity
  have hκn : Real.sqrt κ ≠ 0 := by positivity
  have h2n : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  unfold smallB smallC
  field_simp [hχn, hκn, h2n]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Sound speed: a ~ (2κ/5)u. This uses derivative moment formulas, not
formal differentiation of ρ ~ ρ₀u^(5/2). -/
theorem tendsto_kineticSlope_over_u (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun u => kineticSlope κ χ u / u) (𝓝[>] (0 : ℝ)) (𝓝 (2 * κ / 5)) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hA := tendsto_momentA_low κ χ hκ hχ
  have hB := tendsto_momentB_low κ χ hκ hχ
  have hC := tendsto_momentC_low κ χ hκ hχ
  have hn : 4 * (0 ^ 2 * smallA κ χ) + 5 * (0 * smallB κ χ) + smallC κ χ ≠ 0 := by
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_add]
    unfold smallC
    positivity
  have ht := (((hu.mul hA).const_mul 4).div_const 3 |>.add hB).div
    ((((hu.pow 2).mul hA).const_mul 4 |>.add ((hu.mul hB).const_mul 5)).add hC) hn
  have he : (fun u => kineticSlope κ χ u / u) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u => (4 * u * (momentA κ χ u / lowPower 3 u) / 3 + momentB κ χ u / lowPower 1 u) /
        (4 * u ^ 2 * (momentA κ χ u / lowPower 3 u) +
          5 * u * (momentB κ χ u / lowPower 1 u) + momentC κ χ u / (u * Real.sqrt u))) := by
    filter_upwards [eventually_low_parameters κ hκ] with u hp
    exact kineticSlope_low_identity κ χ u hκ hχ hp.1 hp.2
  apply (tendsto_congr' he).mpr
  convert ht using 1 <;> first | rfl | simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, zero_div, zero_add,
    smallB_div_smallC κ χ hκ hχ, mul_assoc]
  funext u
  rfl

/-- The occupation is bounded above by one throughout its physical interval. -/
theorem energyOccupation_le_one (κ χ u q : ℝ) (hχ : 0 ≤ χ) :
    energyOccupation κ χ u q ≤ 1 := by
  unfold energyOccupation occupation
  apply (div_le_one (occupation_den_pos χ _ hχ)).mpr
  have he := Real.exp_pos (q / beta κ u - u)
  have hm := mul_nonneg hχ he.le
  linarith

/-- A coarse integrable bound for C, sufficient for the relativistic limits.
The sharper logarithmic estimate is proved separately below. -/
theorem momentC_le_two_sqrt_cutoff (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    momentC κ χ u ≤ 2 * Real.sqrt (cutoff κ u) := by
  have hL := cutoff_pos κ u hκ hu hδ
  have hi := intervalIntegrable_momentC κ χ u hκ hχ hu hδ
  have hj := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := cutoff κ u)
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hL.le hi hj
    (fun q hq => show energyOccupation κ χ u q / sigma q ≤ q ^ (-(1 / 2 : ℝ)) from by
      have hs := sigma_pos q hq.1
      have hsq := Real.sqrt_pos.mpr hq.1
      have hσ : Real.sqrt q ≤ sigma q := by
        unfold sigma
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg q, hq.1]
      rw [Real.rpow_neg hq.1.le, ← Real.sqrt_eq_rpow]
      calc
        energyOccupation κ χ u q / sigma q ≤ 1 / sigma q :=
          (div_le_div_iff_of_pos_right hs).mpr (energyOccupation_le_one κ χ u q hχ)
        _ ≤ 1 / Real.sqrt q := one_div_le_one_div_of_le hsq hσ
        _ = (Real.sqrt q)⁻¹ := one_div _)
  unfold momentC
  apply hm.trans_eq
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  ring

theorem eventually_high_parameters (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 1 ∧
      0 < highParameter κ δ ∧ 0 < 1 - κ * highParameter κ δ := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with δ hδ h1
  have he : 1 - κ * highParameter κ δ = δ := by
    unfold highParameter
    field_simp <;> ring
  exact ⟨hδ, h1, div_pos (sub_pos.mpr h1) hκ, by rwa [he]⟩

/-- δ⁴C -> 0; the coarse square-root bound already suffices. -/
theorem tendsto_momentC_high_negligible (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun δ => δ ^ 4 * momentC κ χ (highParameter κ δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hu : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun δ : ℝ => 2 * δ ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hu.pow 3).const_mul 2
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [eventually_high_parameters κ hκ] with δ hd
    exact mul_nonneg (pow_nonneg hd.1.le _) (momentC_nonneg κ χ _ hκ hχ hd.2.2.1 hd.2.2.2)
  · filter_upwards [eventually_high_parameters κ hκ] with δ hd
    have hδ : 0 < δ := hd.1
    have hL : Real.sqrt (cutoff κ (highParameter κ δ)) ≤ 1 / δ := by
      rw [high_cutoff κ δ (ne_of_gt hκ) (ne_of_gt hδ)]
      apply (Real.sqrt_le_iff).mpr
      constructor
      · positivity
      · apply (div_le_iff₀ hδ).mpr
        have hi : 1 ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by simpa using hd.2.1.le)
        have he : (1 / δ) ^ 2 * δ = 1 / δ := by field_simp <;> ring
        rw [he]
        linarith
    calc
      δ ^ 4 * momentC κ χ (highParameter κ δ) ≤ δ ^ 4 * (2 * Real.sqrt (cutoff κ (highParameter κ δ))) :=
        mul_le_mul_of_nonneg_left (momentC_le_two_sqrt_cutoff κ χ _ hκ hχ hd.2.2.1 hd.2.2.2) (by positivity)
      _ ≤ δ ^ 4 * (2 * (1 / δ)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * δ ^ 3 := by field_simp <;> ring

/-- Radiation ratio at the relativistic endpoint. -/
theorem tendsto_kineticW_high (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun δ => kineticW κ χ (highParameter κ δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 3 : ℝ)) := by
  have hu : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun δ => δ ^ 4 * momentA κ χ (highParameter κ δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (highMomentCoefficient 3 κ χ)) := tendsto_sigmaMoment_high 3 κ χ hκ hχ
  have hB : Tendsto (fun δ => δ ^ 4 * momentB κ χ (highParameter κ δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hb := tendsto_sigmaMoment_high 1 κ χ hκ hχ
    have ht := (hu.pow 2).mul hb
    convert ht using 1 <;> try rfl
    all_goals simp [sigmaMoment, momentB, pow_one]
    all_goals ring
  have hI := highMomentCoefficient_pos 3 κ χ hκ hχ
  have hn : 3 * (highMomentCoefficient 3 κ χ + 0) ≠ 0 := by positivity
  have ht := hA.div ((hA.add hB).const_mul 3) hn
  have he : (fun δ => kineticW κ χ (highParameter κ δ)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ => (δ ^ 4 * momentA κ χ (highParameter κ δ)) /
        (3 * (δ ^ 4 * momentA κ χ (highParameter κ δ) + δ ^ 4 * momentB κ χ (highParameter κ δ)))) := by
    filter_upwards [self_mem_nhdsWithin] with δ hd
    have hδ : δ ≠ 0 := ne_of_gt (show 0 < δ from hd)
    unfold kineticW
    rw [← mul_add, mul_left_comm (3 : ℝ), mul_div_mul_left _ _ (pow_ne_zero 4 hδ)]
  apply (tendsto_congr' he).mpr
  have hv : highMomentCoefficient 3 κ χ / (3 * (highMomentCoefficient 3 κ χ + 0)) = (1 / 3 : ℝ) := by
    field_simp
    ring
  rwa [hv] at ht

/-- Sound speed at the relativistic endpoint. -/
theorem tendsto_kineticSlope_high (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun δ => kineticSlope κ χ (highParameter κ δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 3 : ℝ)) := by
  have hu : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun δ => δ ^ 4 * momentA κ χ (highParameter κ δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (highMomentCoefficient 3 κ χ)) := tendsto_sigmaMoment_high 3 κ χ hκ hχ
  have hB : Tendsto (fun δ => δ ^ 4 * momentB κ χ (highParameter κ δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht := (hu.pow 2).mul (tendsto_sigmaMoment_high 1 κ χ hκ hχ)
    convert ht using 1 <;> try rfl
    all_goals simp [sigmaMoment, momentB, pow_one]
    all_goals ring
  have hC := tendsto_momentC_high_negligible κ χ hκ hχ
  have hI := highMomentCoefficient_pos 3 κ χ hκ hχ
  have hn : 4 * highMomentCoefficient 3 κ χ + 5 * 0 + 0 ≠ 0 := by positivity
  have ht := (((hA.const_mul 4).div_const 3).add hB).div
    (((hA.const_mul 4).add (hB.const_mul 5)).add hC) hn
  have he : (fun δ => kineticSlope κ χ (highParameter κ δ)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ => (4 * (δ ^ 4 * momentA κ χ (highParameter κ δ)) / 3 + δ ^ 4 * momentB κ χ (highParameter κ δ)) /
        (4 * (δ ^ 4 * momentA κ χ (highParameter κ δ)) + 5 * (δ ^ 4 * momentB κ χ (highParameter κ δ)) +
          δ ^ 4 * momentC κ χ (highParameter κ δ))) := by
    filter_upwards [self_mem_nhdsWithin] with δ hd
    have hδ : δ ≠ 0 := ne_of_gt (show 0 < δ from hd)
    unfold kineticSlope
    have he : 4 * (δ ^ 4 * momentA κ χ (highParameter κ δ)) / 3 + δ ^ 4 * momentB κ χ (highParameter κ δ) =
        δ ^ 4 * (4 * momentA κ χ (highParameter κ δ) / 3 + momentB κ χ (highParameter κ δ)) := by ring
    rw [he]
    have hden : 4 * (δ ^ 4 * momentA κ χ (highParameter κ δ)) + 5 * (δ ^ 4 * momentB κ χ (highParameter κ δ)) + δ ^ 4 * momentC κ χ (highParameter κ δ) =
        δ ^ 4 * (4 * momentA κ χ (highParameter κ δ) + 5 * momentB κ χ (highParameter κ δ) + momentC κ χ (highParameter κ δ)) := by ring
    rw [hden, mul_div_mul_left _ _ (pow_ne_zero 4 hδ)]
  apply (tendsto_congr' he).mpr
  have hv : (4 * highMomentCoefficient 3 κ χ / 3 + 0) / (4 * highMomentCoefficient 3 κ χ + 5 * 0 + 0) = (1 / 3 : ℝ) := by
    field_simp
    ring
  rwa [hv] at ht
/-- The slope-to-pressure ratio tends to the polytropic exponent 7/5. -/
theorem tendsto_kineticSlope_div_W_low (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (fun u => kineticSlope κ χ u / kineticW κ χ u)
      (𝓝[>] (0 : ℝ)) (𝓝 (7 / 5 : ℝ)) := by
  have hn : 2 * κ / 7 ≠ 0 := by positivity
  have ht := (tendsto_kineticSlope_over_u κ χ hκ hχ).div
    (tendsto_kineticW_over_u κ χ hκ hχ) hn
  have he : (fun u => kineticSlope κ χ u / kineticW κ χ u) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u => (kineticSlope κ χ u / u) / (kineticW κ χ u / u)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [div_div_div_cancel_right₀ (ne_of_gt (show 0 < u from hu))]
  apply (tendsto_congr' he).mpr
  have hv : (2 * κ / 5) / (2 * κ / 7) = (7 / 5 : ℝ) := by field_simp <;> ring
  rwa [hv] at ht

theorem tendsto_kineticW_relativistic (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (kineticW κ χ) (𝓝[<] (1 / κ)) (𝓝 (1 / 3 : ℝ)) := by
  have ht := (tendsto_kineticW_high κ χ hκ hχ).comp (tendsto_delta_endpoint κ hκ)
  dsimp only [Function.comp_def] at ht
  simpa only [highParameter_delta κ _ (ne_of_gt hκ)] using ht

theorem tendsto_kineticSlope_relativistic (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Tendsto (kineticSlope κ χ) (𝓝[<] (1 / κ)) (𝓝 (1 / 3 : ℝ)) := by
  have ht := (tendsto_kineticSlope_high κ χ hκ hχ).comp (tendsto_delta_endpoint κ hκ)
  dsimp only [Function.comp_def] at ht
  simpa only [highParameter_delta κ _ (ne_of_gt hκ)] using ht

theorem rhoInfinity_pos (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) : 0 < rhoInfinity κ χ mf c hp := by
  rw [rhoInfinity_eq]
  exact mul_pos (kineticConstant_pos mf c hp hmf hc hhp) (highMomentCoefficient_pos 3 κ χ hκ hχ)

/-- The actual density diverges as u approaches 1/κ from below. -/
theorem tendsto_densityEnergy_atTop (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    Tendsto (fun u => densityEnergy κ χ u mf c hp) (𝓝[<] (1 / κ)) atTop := by
  have hd := tendsto_delta_endpoint κ hκ
  have hi : Tendsto (fun u => ((1 - κ * u)⁻¹) ^ 4) (𝓝[<] (1 / κ)) atTop :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp (tendsto_inv_nhdsGT_zero.comp hd)
  have ht := (tendsto_densityEnergy_relativistic κ χ mf c hp hκ hχ).pos_mul_atTop
    (rhoInfinity_pos κ χ mf c hp hκ hχ hmf hc hhp) hi
  have he : (fun u => densityEnergy κ χ u mf c hp) =ᶠ[𝓝[<] (1 / κ)]
      (fun u => ((1 - κ * u) ^ 4 * densityEnergy κ χ u mf c hp) * ((1 - κ * u)⁻¹) ^ 4) := by
    filter_upwards [hd.eventually self_mem_nhdsWithin] with u hu
    have hn : 1 - κ * u ≠ 0 := ne_of_gt (show 0 < 1 - κ * u from hu)
    field_simp
  exact (tendsto_congr' he).mpr ht

/-- P/ρ -> c²/3 along the actual parametric EOS. -/
theorem tendsto_pressure_div_density_relativistic (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    Tendsto (fun u => pressureEnergy κ χ u mf c hp / densityEnergy κ χ u mf c hp)
      (𝓝[<] (1 / κ)) (𝓝 (c ^ 2 / 3)) := by
  have hρ := rhoInfinity_pos κ χ mf c hp hκ hχ hmf hc hhp
  have ht := (tendsto_pressureEnergy_relativistic κ χ mf c hp hκ hχ).div
    (tendsto_densityEnergy_relativistic κ χ mf c hp hκ hχ) (ne_of_gt hρ)
  have he : (fun u => pressureEnergy κ χ u mf c hp / densityEnergy κ χ u mf c hp) =ᶠ[𝓝[<] (1 / κ)]
      (fun u => ((1 - κ * u) ^ 4 * pressureEnergy κ χ u mf c hp) /
        ((1 - κ * u) ^ 4 * densityEnergy κ χ u mf c hp)) := by
    filter_upwards [(tendsto_delta_endpoint κ hκ).eventually self_mem_nhdsWithin] with u hu
    rw [mul_div_mul_left _ _ (pow_ne_zero 4 (ne_of_gt (show 0 < 1 - κ * u from hu)))]
  apply (tendsto_congr' he).mpr
  have hv : (c ^ 2 * rhoInfinity κ χ mf c hp / 3) / rhoInfinity κ χ mf c hp = c ^ 2 / 3 := by
    field_simp

  rwa [hv] at ht
/-- Convert a nonzero leading coefficient into the standard `IsEquivalent` relation. -/
theorem isEquivalent_of_scaled_limit {f g : ℝ → ℝ} {l : Filter ℝ} {C : ℝ}
    (hC : C ≠ 0) (hg : ∀ᶠ u in l, g u ≠ 0)
    (ht : Tendsto (fun u => f u / g u) l (𝓝 C)) :
    Asymptotics.IsEquivalent l f (fun u => C * g u) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one (hg.mono (fun u hu => mul_ne_zero hC hu))).mpr
  have h := ht.div_const C
  convert h using 1 <;> first | rfl | (funext u; simp only [Pi.div_apply, div_div, mul_comm]) | simp only [div_self hC]

theorem rho0_pos (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) : 0 < rho0 κ χ mf c hp := by
  rw [rho0_eq κ χ mf c hp hκ hχ (ne_of_gt hhp)]
  have hk := kineticConstant_pos mf c hp hmf hc hhp
  unfold smallB
  positivity

theorem pressure0_pos (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) : 0 < pressure0 κ χ mf c hp := by
  rw [pressure0_eq κ χ mf c hp hκ hχ (ne_of_gt hhp)]
  have hk := kineticConstant_pos mf c hp hmf hc hhp
  unfold smallA
  positivity

/-- ρ(u) ~ ρ₀u^(5/2), in Mathlib's asymptotic-equivalence relation. -/
theorem densityEnergy_low_asymptotic (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ)) (fun u => densityEnergy κ χ u mf c hp)
      (fun u => rho0 κ χ mf c hp * Real.rpow u (5 / 2 : ℝ)) := by
  apply isEquivalent_of_scaled_limit (ne_of_gt (rho0_pos κ χ mf c hp hκ hχ hmf hc hhp))
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact ne_of_gt (Real.rpow_pos_of_pos (show 0 < u from hu) _)
  · exact tendsto_densityEnergy_low κ χ mf c hp hκ hχ (ne_of_gt hhp)

/-- P(u) ~ P₀u^(7/2). -/
theorem pressureEnergy_low_asymptotic (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ)) (fun u => pressureEnergy κ χ u mf c hp)
      (fun u => pressure0 κ χ mf c hp * Real.rpow u (7 / 2 : ℝ)) := by
  apply isEquivalent_of_scaled_limit (ne_of_gt (pressure0_pos κ χ mf c hp hκ hχ hmf hc hhp))
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact ne_of_gt (Real.rpow_pos_of_pos (show 0 < u from hu) _)
  · exact tendsto_pressureEnergy_low κ χ mf c hp hκ hχ (ne_of_gt hhp)

/-- The 7/5 polytropic law after eliminating u, along the parametric EOS. -/
theorem tendsto_polytropic_ratio_low (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    Tendsto (fun u => pressureEnergy κ χ u mf c hp /
      (pressure0 κ χ mf c hp * Real.rpow (densityEnergy κ χ u mf c hp / rho0 κ χ mf c hp) (7 / 5 : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hρ := rho0_pos κ χ mf c hp hκ hχ hmf hc hhp
  have hP := pressure0_pos κ χ mf c hp hκ hχ hmf hc hhp
  have hD : Tendsto (fun u => (densityEnergy κ χ u mf c hp / Real.rpow u (5 / 2 : ℝ)) / rho0 κ χ mf c hp)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [div_self (ne_of_gt hρ)] using
      (tendsto_densityEnergy_low κ χ mf c hp hκ hχ (ne_of_gt hhp)).div_const (rho0 κ χ mf c hp)
  have hN : Tendsto (fun u => (pressureEnergy κ χ u mf c hp / Real.rpow u (7 / 2 : ℝ)) / pressure0 κ χ mf c hp)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [div_self (ne_of_gt hP)] using
      (tendsto_pressureEnergy_low κ χ mf c hp hκ hχ (ne_of_gt hhp)).div_const (pressure0 κ χ mf c hp)
  have ht := hN.div (hD.rpow_const (p := (7 / 5 : ℝ)) (Or.inl (by norm_num))) (by norm_num : Real.rpow 1 (7 / 5 : ℝ) ≠ 0)
  have he : (fun u => pressureEnergy κ χ u mf c hp /
      (pressure0 κ χ mf c hp * Real.rpow (densityEnergy κ χ u mf c hp / rho0 κ χ mf c hp) (7 / 5 : ℝ))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u => ((pressureEnergy κ χ u mf c hp / Real.rpow u (7 / 2 : ℝ)) / pressure0 κ χ mf c hp) /
        Real.rpow ((densityEnergy κ χ u mf c hp / Real.rpow u (5 / 2 : ℝ)) / rho0 κ χ mf c hp) (7 / 5 : ℝ)) := by
    filter_upwards [eventually_low_parameters κ hκ] with u hu
    have hp5 := Real.rpow_pos_of_pos hu.1 (5 / 2 : ℝ)
    have hp7 := Real.rpow_pos_of_pos hu.1 (7 / 2 : ℝ)
    have hr : 0 < densityEnergy κ χ u mf c hp := by
      unfold densityEnergy
      exact mul_pos (kineticConstant_pos mf c hp hmf hc hhp)
        (add_pos (momentA_pos κ χ u hκ hχ hu.1 hu.2) (momentB_pos κ χ u hκ hχ hu.1 hu.2))
    have hqpos : 0 < ((densityEnergy κ χ u mf c hp / Real.rpow u (5 / 2 : ℝ)) / rho0 κ χ mf c hp) :=
      div_pos (div_pos hr hp5) hρ
    have hid : densityEnergy κ χ u mf c hp / rho0 κ χ mf c hp =
        Real.rpow u (5 / 2 : ℝ) * ((densityEnergy κ χ u mf c hp / Real.rpow u (5 / 2 : ℝ)) / rho0 κ χ mf c hp) := by
      field_simp [ne_of_gt hp5]

    rw [hid]
    change _ / (_ * ((u ^ (5 / 2 : ℝ)) * _) ^ (7 / 5 : ℝ)) = _
    rw [Real.mul_rpow hp5.le hqpos.le, ← Real.rpow_mul hu.1.le]
    have hexp : (5 / 2 : ℝ) * (7 / 5 : ℝ) = 7 / 2 := by norm_num
    rw [hexp]
    simp only [div_div]
    congr 1
    ring_nf
    rfl
  apply (tendsto_congr' he).mpr
  convert ht using 1 <;> first | rfl | simp only [Real.one_rpow, div_one]

/-- Standard asymptotic equivalence for the 7/5 polytropic law. -/
theorem polytropic_low_asymptotic (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ)) (fun u => pressureEnergy κ χ u mf c hp)
      (fun u => pressure0 κ χ mf c hp * Real.rpow (densityEnergy κ χ u mf c hp / rho0 κ χ mf c hp) (7 / 5 : ℝ)) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr
  · exact tendsto_polytropic_ratio_low κ χ mf c hp hκ hχ hmf hc hhp
  · filter_upwards [eventually_low_parameters κ hκ] with u hu
    have hr : 0 < densityEnergy κ χ u mf c hp := by
      unfold densityEnergy
      exact mul_pos (kineticConstant_pos mf c hp hmf hc hhp)
        (add_pos (momentA_pos κ χ u hκ hχ hu.1 hu.2) (momentB_pos κ χ u hκ hχ hu.1 hu.2))
    exact mul_ne_zero (ne_of_gt (pressure0_pos κ χ mf c hp hκ hχ hmf hc hhp))
      (ne_of_gt (Real.rpow_pos_of_pos (div_pos hr (rho0_pos κ χ mf c hp hκ hχ hmf hc hhp)) _))
/-- ρ(u) ~ ρ∞/(1−κu)^4. -/
theorem densityEnergy_relativistic_asymptotic (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    Asymptotics.IsEquivalent (𝓝[<] (1 / κ)) (fun u => densityEnergy κ χ u mf c hp)
      (fun u => rhoInfinity κ χ mf c hp / (1 - κ * u) ^ 4) := by
  change Asymptotics.IsEquivalent _ _ (fun u => rhoInfinity κ χ mf c hp * ((1 - κ * u) ^ 4)⁻¹)
  apply isEquivalent_of_scaled_limit (ne_of_gt (rhoInfinity_pos κ χ mf c hp hκ hχ hmf hc hhp))
  · filter_upwards [(tendsto_delta_endpoint κ hκ).eventually self_mem_nhdsWithin] with u hu
    exact inv_ne_zero (pow_ne_zero 4 (ne_of_gt (show 0 < 1 - κ * u from hu)))
  · simpa only [div_inv_eq_mul, mul_comm] using tendsto_densityEnergy_relativistic κ χ mf c hp hκ hχ

/-- P(u) ~ (c²ρ∞/3)/(1−κu)^4. -/
theorem pressureEnergy_relativistic_asymptotic (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    Asymptotics.IsEquivalent (𝓝[<] (1 / κ)) (fun u => pressureEnergy κ χ u mf c hp)
      (fun u => (c ^ 2 * rhoInfinity κ χ mf c hp / 3) / (1 - κ * u) ^ 4) := by
  change Asymptotics.IsEquivalent _ _ (fun u => (c ^ 2 * rhoInfinity κ χ mf c hp / 3) * ((1 - κ * u) ^ 4)⁻¹)
  have hρ := rhoInfinity_pos κ χ mf c hp hκ hχ hmf hc hhp
  apply isEquivalent_of_scaled_limit (by positivity)
  · filter_upwards [(tendsto_delta_endpoint κ hκ).eventually self_mem_nhdsWithin] with u hu
    exact inv_ne_zero (pow_ne_zero 4 (ne_of_gt (show 0 < 1 - κ * u from hu)))
  · simpa only [div_inv_eq_mul, mul_comm] using tendsto_pressureEnergy_relativistic κ χ mf c hp hκ hχ

/-- P ~ (c²/3)ρ, along the EOS, where the density tends to infinity. -/
theorem radiation_relativistic_asymptotic (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    Asymptotics.IsEquivalent (𝓝[<] (1 / κ)) (fun u => pressureEnergy κ χ u mf c hp)
      (fun u => c ^ 2 / 3 * densityEnergy κ χ u mf c hp) := by
  apply isEquivalent_of_scaled_limit (by positivity)
  · filter_upwards [(tendsto_densityEnergy_atTop κ χ mf c hp hκ hχ hmf hc hhp).eventually_gt_atTop 0] with u hu
    exact ne_of_gt hu
  · exact tendsto_pressure_div_density_relativistic κ χ mf c hp hκ hχ hmf hc hhp

/-- The low-density branch really approaches vacuum. -/
theorem tendsto_densityEnergy_zero (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hhp : hp ≠ 0) :
    Tendsto (fun u => densityEnergy κ χ u mf c hp) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have ht := (tendsto_densityEnergy_low κ χ mf c hp hκ hχ hhp).mul
    (hu.rpow_const (p := (5 / 2 : ℝ)) (Or.inr (by norm_num)))
  have he : (fun u => densityEnergy κ χ u mf c hp) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u => (densityEnergy κ χ u mf c hp / Real.rpow u (5 / 2 : ℝ)) * Real.rpow u (5 / 2 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos (show 0 < u from hu) _))).symm
  apply (tendsto_congr' he).mpr
  simpa using ht
/-- Universal square-root estimate for the integrable inverse kinetic weight. -/
theorem integral_inv_sigma_le_two_sqrt (L : ℝ) (hL : 0 ≤ L) :
    (∫ q in (0 : ℝ)..L, 1 / sigma q) ≤ 2 * Real.sqrt L := by
  have hi := intervalIntegrable_inv_sigma L hL
  have hj := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := L)
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hL hi hj
    (fun q hq => show 1 / sigma q ≤ q ^ (-(1 / 2 : ℝ)) from by
      have hσ : Real.sqrt q ≤ sigma q := by
        unfold sigma
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg q, hq.1]
      rw [Real.rpow_neg hq.1.le, ← Real.sqrt_eq_rpow]
      simpa only [one_div] using one_div_le_one_div_of_le (Real.sqrt_pos.mpr hq.1) hσ)
  apply hm.trans_eq
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  ring

/-- A logarithmic estimate for the inverse kinetic weight, obtained by splitting
at q=1. No formula for arcosh is needed. -/
theorem integral_inv_sigma_le_log (L : ℝ) (hL : 1 ≤ L) :
    (∫ q in (0 : ℝ)..L, 1 / sigma q) ≤ 2 + Real.log L := by
  have hi01 := intervalIntegrable_inv_sigma 1 (by norm_num)
  have hi0L := intervalIntegrable_inv_sigma L (by linarith)
  have hi1L := hi01.symm.trans hi0L
  have hqpos : ∀ q ∈ uIcc (1 : ℝ) L, 0 < q := by
    rw [uIcc_of_le hL]
    intro q hq
    linarith [hq.1]
  have hj : IntervalIntegrable (fun q : ℝ => 1 / q) volume 1 L := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div continuousOn_id (fun q hq => ne_of_gt (hqpos q hq))
  have hm : (∫ q in (1 : ℝ)..L, 1 / sigma q) ≤ Real.log L := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo hL hi1L hj
      (fun q hq => show 1 / sigma q ≤ 1 / q from by
        have hqp : 0 < q := by linarith [hq.1]
        have hσ : q ≤ sigma q := by
          calc
            q = Real.sqrt (q ^ 2) := (Real.sqrt_sq hqp.le).symm
            _ ≤ sigma q := by
              unfold sigma
              apply Real.sqrt_le_sqrt
              nlinarith
        exact one_div_le_one_div_of_le hqp hσ)
    simpa only [integral_one_div_of_pos (by norm_num : (0 : ℝ) < 1) (by linarith : 0 < L), div_one] using hh
  rw [← intervalIntegral.integral_add_adjacent_intervals hi01 hi1L]
  have hs := integral_inv_sigma_le_two_sqrt 1 (by norm_num)
  norm_num at hs
  simp only [one_div] at hm ⊢
  linarith

/-- C is bounded by the inverse kinetic weight because 0≤f≤1. -/
theorem momentC_le_integral_inv_sigma (κ χ u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : 0 < u) (hδ : 0 < 1 - κ * u) :
    momentC κ χ u ≤ (∫ q in (0 : ℝ)..cutoff κ u, 1 / sigma q) := by
  apply intervalIntegral.integral_mono_on_of_le_Ioo
    (cutoff_pos κ u hκ hu hδ).le
    (intervalIntegrable_momentC κ χ u hκ hχ hu hδ)
    (intervalIntegrable_inv_sigma _ (cutoff_pos κ u hκ hu hδ).le)
  intro q hq
  exact (div_le_div_iff_of_pos_right (sigma_pos q hq.1)).mpr
    (energyOccupation_le_one κ χ u q hχ)

/-- The explicit relativistic logarithmic bound for C. -/
theorem momentC_high_le_log (κ χ δ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    momentC κ χ (highParameter κ δ) ≤ 2 + Real.log (1 / δ) := by
  have hu : 0 < highParameter κ δ := div_pos (by linarith) hκ
  have hd : 0 < 1 - κ * highParameter κ δ := by
    have he : 1 - κ * highParameter κ δ = δ := by unfold highParameter; field_simp <;> ring
    rwa [he]
  have hL : 1 ≤ cutoff κ (highParameter κ δ) := by
    rw [high_cutoff κ δ (ne_of_gt hκ) (ne_of_gt hδ)]
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hLle : cutoff κ (highParameter κ δ) ≤ 1 / δ := by
    rw [high_cutoff κ δ (ne_of_gt hκ) (ne_of_gt hδ)]
    exact (div_le_div_iff_of_pos_right hδ).mpr (by linarith)
  calc
    momentC κ χ (highParameter κ δ) ≤ ∫ q in (0 : ℝ)..cutoff κ (highParameter κ δ), 1 / sigma q :=
      momentC_le_integral_inv_sigma κ χ _ hκ hχ hu hd
    _ ≤ 2 + Real.log (cutoff κ (highParameter κ δ)) := integral_inv_sigma_le_log _ hL
    _ ≤ 2 + Real.log (1 / δ) := add_le_add_right (Real.log_le_log (by linarith) hLle) 2

/-- The manuscript's C = O(log(1/δ)) bound in Mathlib's Big-O relation. -/
theorem momentC_high_isBigO_log (κ χ : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    Asymptotics.IsBigO (𝓝[>] (0 : ℝ)) (fun δ => momentC κ χ (highParameter κ δ))
      (fun δ => Real.log (1 / δ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨3, ?_⟩
  have hl : Tendsto (fun δ : ℝ => Real.log (1 / δ)) (𝓝[>] (0 : ℝ)) atTop := by
    convert Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero using 1
    funext δ
    simp only [Function.comp_def, one_div]
  filter_upwards [eventually_high_parameters κ hκ, hl.eventually_ge_atTop 1,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with δ hd hlog hhalf
  have hC := momentC_nonneg κ χ _ hκ hχ hd.2.2.1 hd.2.2.2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC, abs_of_nonneg (by linarith : 0 ≤ Real.log (1 / δ))]
  have hupper := momentC_high_le_log κ χ δ hκ hχ hd.1 hhalf.le
  linarith
/-- The low-density limit of the actual derivative ratio dΠ/dρ, Π=P/c². -/
theorem tendsto_EOS_derivative_ratio_over_u (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hK : kineticConstant mf c hp ≠ 0) :
    Tendsto (fun u => (deriv (fun v => pressureMass κ χ v mf c hp) u /
        deriv (fun v => densityEnergy κ χ v mf c hp) u) / u)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * κ / 5)) := by
  have he : (fun u => (deriv (fun v => pressureMass κ χ v mf c hp) u /
      deriv (fun v => densityEnergy κ χ v mf c hp) u) / u) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u => kineticSlope κ χ u / u) := by
    filter_upwards [eventually_low_parameters κ hκ] with u hu
    rw [EOS_derivative_ratio κ χ u mf c hp hκ hχ hu.1 hu.2 hK]
    rfl
  exact (tendsto_congr' he).mpr (tendsto_kineticSlope_over_u κ χ hκ hχ)

/-- The physical parameters hold eventually on the left endpoint neighborhood. -/
theorem eventually_relativistic_parameters (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ u in 𝓝[<] (1 / κ), 0 < u ∧ 0 < 1 - κ * u := by
  have hd := tendsto_delta_endpoint κ hκ
  filter_upwards [hd.eventually (eventually_high_parameters κ hκ)] with u hu
  exact ⟨by simpa only [highParameter_delta κ _ (ne_of_gt hκ)] using hu.2.2.1, hu.1⟩

/-- The relativistic limit of the actual derivative ratio dΠ/dρ. -/
theorem tendsto_EOS_derivative_ratio_relativistic (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hK : kineticConstant mf c hp ≠ 0) :
    Tendsto (fun u => deriv (fun v => pressureMass κ χ v mf c hp) u /
        deriv (fun v => densityEnergy κ χ v mf c hp) u)
      (𝓝[<] (1 / κ)) (𝓝 (1 / 3 : ℝ)) := by
  have he : (fun u => deriv (fun v => pressureMass κ χ v mf c hp) u /
      deriv (fun v => densityEnergy κ χ v mf c hp) u) =ᶠ[𝓝[<] (1 / κ)]
      (kineticSlope κ χ) := by
    filter_upwards [eventually_relativistic_parameters κ hκ] with u hu
    exact EOS_derivative_ratio κ χ u mf c hp hκ hχ hu.1 hu.2 hK
  exact (tendsto_congr' he).mpr (tendsto_kineticSlope_relativistic κ χ hκ hχ)

/-- The low-density coefficient of Π/ρ, from the exact EOS. -/
theorem tendsto_EOS_w_over_u (κ χ mf c hp : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hK : kineticConstant mf c hp ≠ 0) :
    Tendsto (fun u => (pressureMass κ χ u mf c hp / densityEnergy κ χ u mf c hp) / u)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * κ / 7)) := by
  have he : (fun u => (pressureMass κ χ u mf c hp / densityEnergy κ χ u mf c hp) / u) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u => kineticW κ χ u / u) := by
    filter_upwards [eventually_low_parameters κ hκ] with u hu
    rw [EOS_w_ratio_eq_kineticMoments κ χ u mf c hp hκ hχ hu.1 hu.2 hK]
    rfl
  exact (tendsto_congr' he).mpr (tendsto_kineticW_over_u κ χ hκ hχ)

/-! ### TOV existence: EOS regularity and the physical vector field

The center is a singular point of the radius-form TOV equations; interior
Picard--Lindelof alone does not give a regular-center solution. We instead
construct the center solution by a contraction on C([0,1], R).

Write D(u)=4πGρ(u)/c², Q(u)=4πGΠ(u)/c², b(u)=1/β(u),
μ=Gm/c², and r=R t. For a candidate center potential f, set
A_f(t)=∫₀¹ s² D(f(ts)) ds. Then μ(r)=r³ A_f(r/R), and

  (P f)(t) = uc - R² ∫₀ᵗ s b(f(s))
                 (A_f(s)+Q(f(s))) / (1-2R²s² A_f(s)) ds.

C¹ kinetic regularity gives a bounded Lipschitz extension of (D,Q,b) from a
small closed interval around uc. The auxiliary denominator is clamped below
by 1/2. Uniform bounds give a contraction for a strictly positive small R,
keep its fixed point inside the original physical interval, and show that
the clamp is inactive there. Thus the resulting mass and potential satisfy
the actual kinetic TOV equations; neither a TOV path nor EOS regularity is
assumed in the final existence theorem.

Main theorem: `exists_physical_regular_TOV`. Further phase results are
`CenterSeed.phase_wedge` and the three `CenterSeed.tendsto_*` phase theorems.
This section proves local regular-center and local interior existence. It
does not assert a maximal global branch, a finite vacuum surface, or the
uniqueness of all regular-center solutions.
-/

def kineticDomain (κ : ℝ) : Set ℝ := {u | 0 < u ∧ 0 < 1 - κ * u}

theorem isOpen_kineticDomain (κ : ℝ) : IsOpen (kineticDomain κ) :=
  isOpen_lt continuous_const continuous_id |>.inter
    (isOpen_lt continuous_const (continuous_const.sub (continuous_const.mul continuous_id)))

/-- A small translated rectangle remains in the physical kinetic domain. -/
theorem physical_parameter_rectangle (κ u : ℝ) (hκ : 0 < κ) (hu : u ∈ kineticDomain κ) :
    ∃ ε > 0, ∀ v ∈ Icc (-ε) ε, u + v ∈ kineticDomain κ := by
  let ε := min u ((1 - κ * u) / κ) / 2
  have hε : 0 < ε := half_pos (lt_min hu.1 (div_pos hu.2 hκ))
  refine ⟨ε, hε, ?_⟩
  intro v hv
  have he1 : 2 * ε ≤ u := by dsimp [ε]; linarith [min_le_left u ((1 - κ * u) / κ)]
  have he2 : 2 * ε ≤ (1 - κ * u) / κ := by dsimp [ε]; linarith [min_le_right u ((1 - κ * u) / κ)]
  have hk := (le_div_iff₀ hκ).mp he2
  exact ⟨by linarith [hv.1], by nlinarith [hv.2]⟩

/-- Continuity of the actual singular moment at every physical parameter. -/
theorem continuousAt_momentC (κ χ u : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hu : u ∈ kineticDomain κ) : ContinuousAt (momentC κ χ) u := by
  obtain ⟨ε, hε, hp⟩ := physical_parameter_rectangle κ u hκ hu
  let F : ℝ → ℝ → ℝ := fun v t => lowCFactor κ χ (u + v) t
  have hc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc (-ε) ε ×ˢ Icc (0 : ℝ) 1) := by
    have hv : Continuous (fun p : ℝ × ℝ => u + p.1) := continuous_const.add continuous_fst
    have hb : ContinuousOn (fun p : ℝ × ℝ => beta κ (u + p.1))
        (Icc (-ε) ε ×ˢ Icc (0 : ℝ) 1) :=
      continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul hv.continuousOn))
        (fun p h => ne_of_gt (hp p.1 h.1).2)
    have ho := (continuous_lowOccupation χ hχ).comp (hv.prodMk continuous_snd)
    exact (hb.sqrt.mul ho.continuousOn).div
      ((((hb.mul hv.continuousOn).mul continuous_snd.continuousOn).add continuousOn_const).sqrt)
      (fun p h => ne_of_gt (Real.sqrt_pos.mpr (low_sqrt_argument_pos κ _ _ (hp p.1 h.1).2 h.2)))
  have hi := continuousAt_weighted_integral_unit (fun t => Real.rpow t (-(1 / 2 : ℝ))) F ε hε
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))) hc
  have hv : ContinuousAt (fun v : ℝ => u + v) 0 := continuousAt_const.add continuousAt_id
  have hj := (hv.mul hv.sqrt).mul hi
  have he : (fun v => momentC κ χ (u + v)) =ᶠ[𝓝 (0 : ℝ)]
      (fun v => ((u + v) * Real.sqrt (u + v)) *
        (∫ t in (0 : ℝ)..1, Real.rpow t (-(1 / 2 : ℝ)) * F v t)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with v hv
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hv
    have hh := abs_lt.mp hv
    have hpar := hp v ⟨hh.1.le, hh.2.le⟩
    have hid := momentC_low_ratio κ χ (u + v) hκ hpar.1 hpar.2
    have hn : (u + v) * Real.sqrt (u + v) ≠ 0 :=
      mul_ne_zero (ne_of_gt hpar.1) (ne_of_gt (Real.sqrt_pos.mpr hpar.1))
    rw [← hid, mul_div_cancel₀ _ hn]
  have hjc := hj.congr_of_eventuallyEq he
  have hback := hjc.comp_of_eq (f := fun v : ℝ => v - u)
    (continuousAt_id.sub continuousAt_const) (sub_self u)
  simpa only [Function.comp_def, add_sub_cancel] using hback

/-- Density is C¹ throughout the open physical kinetic domain. -/
theorem contDiffOn_densityEnergy (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    ContDiffOn ℝ 1 (fun u => densityEnergy κ χ u mf c hp) (kineticDomain κ) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen (isOpen_kineticDomain κ)]
  refine ⟨?_, by simp, ?_⟩
  · intro u hu
    exact (hasDerivAt_densityEnergy κ χ u mf c hp hκ hχ hu.1 hu.2).differentiableAt.differentiableWithinAt
  · apply contDiffOn_zero.mpr
    have he : EqOn (deriv (fun u => densityEnergy κ χ u mf c hp))
        (fun u => kineticConstant mf c hp * beta κ u *
          (4 * momentA κ χ u + 5 * momentB κ χ u + momentC κ χ u)) (kineticDomain κ) := by
      intro u hu
      exact (hasDerivAt_densityEnergy κ χ u mf c hp hκ hχ hu.1 hu.2).deriv
    apply ContinuousOn.congr ?_ he
    intro u hu
    have hb : ContinuousAt (beta κ) u :=
      continuousAt_const.div (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) (ne_of_gt hu.2)
    have hA := (hasDerivAt_momentA κ χ u hκ hχ hu.1 hu.2).continuousAt
    have hB := (hasDerivAt_momentB κ χ u hκ hχ hu.1 hu.2).continuousAt
    have hC := continuousAt_momentC κ χ u hκ hχ hu
    exact ((continuousAt_const.mul hb).mul
      (((continuousAt_const.mul hA).add (continuousAt_const.mul hB)).add hC)).continuousWithinAt

/-- The mass-unit pressure Π=P/c² is C¹ on the same domain. -/
theorem contDiffOn_pressureMass (κ χ mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    ContDiffOn ℝ 1 (fun u => pressureMass κ χ u mf c hp) (kineticDomain κ) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen (isOpen_kineticDomain κ)]
  refine ⟨?_, by simp, ?_⟩
  · intro u hu
    exact (hasDerivAt_pressureMass κ χ u mf c hp hκ hχ hu.1 hu.2).differentiableAt.differentiableWithinAt
  · apply contDiffOn_zero.mpr
    have he : EqOn (deriv (fun u => pressureMass κ χ u mf c hp))
        (fun u => kineticConstant mf c hp * beta κ u * (4 * momentA κ χ u / 3 + momentB κ χ u))
        (kineticDomain κ) := by
      intro u hu
      exact (hasDerivAt_pressureMass κ χ u mf c hp hκ hχ hu.1 hu.2).deriv
    apply ContinuousOn.congr ?_ he
    intro u hu
    have hb : ContinuousAt (beta κ) u :=
      continuousAt_const.div (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) (ne_of_gt hu.2)
    have hA := (hasDerivAt_momentA κ χ u hκ hχ hu.1 hu.2).continuousAt
    have hB := (hasDerivAt_momentB κ χ u hκ hχ hu.1 hu.2).continuousAt
    exact ((continuousAt_const.mul hb).mul
      (((continuousAt_const.mul hA).div_const 3).add hB)).continuousWithinAt

abbrev TOVState := ℝ × (ℝ × ℝ)

def compactnessRatio (G c r m : ℝ) : ℝ := 2 * G * m / (r * c ^ 2)

def tovDomain (κ G c : ℝ) : Set TOVState :=
  {p | 0 < p.1 ∧ 0 < p.2.1 ∧ p.2.2 ∈ kineticDomain κ ∧ compactnessRatio G c p.1 p.2.1 < 1}

/-- Autonomous lift: radius, mass, and kinetic potential. Its radius component
is one, so the independent variable is the physical radius. -/
def tovField (κ χ mf G c hp : ℝ) (p : TOVState) : TOVState :=
  (1, (4 * Real.pi * p.1 ^ 2 * densityEnergy κ χ p.2.2 mf c hp,
    -G * (p.2.1 + 4 * Real.pi * p.1 ^ 3 * pressureMass κ χ p.2.2 mf c hp) /
      (c ^ 2 * p.1 ^ 2 * beta κ p.2.2 * (1 - compactnessRatio G c p.1 p.2.1))))

/-- The genuine kinetic TOV vector field is C¹ at each physical interior state. -/
theorem contDiffAt_tovField (κ χ mf G c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hc : c ≠ 0) (p : TOVState) (hpar : p ∈ tovDomain κ G c) :
    ContDiffAt ℝ 1 (tovField κ χ mf G c hp) p := by
  have hr : ContDiffAt ℝ 1 (fun q : TOVState => q.1) p := contDiffAt_fst
  have hm : ContDiffAt ℝ 1 (fun q : TOVState => q.2.1) p := contDiffAt_fst.comp p contDiffAt_snd
  have hu : ContDiffAt ℝ 1 (fun q : TOVState => q.2.2) p := contDiffAt_snd.comp p contDiffAt_snd
  have hρ := ((contDiffOn_densityEnergy κ χ mf c hp hκ hχ).contDiffAt
    ((isOpen_kineticDomain κ).mem_nhds hpar.2.2.1)).comp p hu
  have hPress := ((contDiffOn_pressureMass κ χ mf c hp hκ hχ).contDiffAt
    ((isOpen_kineticDomain κ).mem_nhds hpar.2.2.1)).comp p hu
  have hβ : ContDiffAt ℝ 1 (fun q : TOVState => beta κ q.2.2) p :=
    contDiffAt_const.div (contDiffAt_const.sub (contDiffAt_const.mul hu)) (ne_of_gt hpar.2.2.1.2)
  have hx : ContDiffAt ℝ 1 (fun q : TOVState => compactnessRatio G c q.1 q.2.1) p :=
    ((contDiffAt_const.mul hm).div (hr.mul contDiffAt_const) (mul_ne_zero (ne_of_gt hpar.1) (pow_ne_zero 2 hc)))
  have hden : c ^ 2 * p.1 ^ 2 * beta κ p.2.2 * (1 - compactnessRatio G c p.1 p.2.1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 (ne_of_gt hpar.1)))
      (ne_of_gt (div_pos hκ hpar.2.2.1.2))) (ne_of_gt (sub_pos.mpr hpar.2.2.2))
  exact contDiffAt_const.prodMk
    (((contDiffAt_const.mul (hr.pow 2)).mul hρ).prodMk
      ((contDiffAt_const.mul (hm.add ((contDiffAt_const.mul (hr.pow 3)).mul hPress))).div
        (((contDiffAt_const.mul (hr.pow 2)).mul hβ).mul (contDiffAt_const.sub hx)) hden))

/-- Local existence at every positive radius with positive mass, physical
kinetic parameter, and horizon-free initial data. -/
theorem exists_tov_interior (κ χ mf G c hp r₀ m₀ u₀ : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hc : c ≠ 0)
    (hinit : (r₀, (m₀, u₀)) ∈ tovDomain κ G c) :
    ∃ f : ℝ → TOVState, f r₀ = (r₀, (m₀, u₀)) ∧
      ∃ ε > 0, ∀ r ∈ Ioo (r₀ - ε) (r₀ + ε),
        HasDerivAt f (tovField κ χ mf G c hp (f r)) r := by
  exact ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    (contDiffAt_tovField κ χ mf G c hp hκ hχ hc _ hinit) r₀

/-- The radius component of the lifted solution is exactly the independent radius. -/
theorem tov_radius_eq (κ χ mf G c hp r₀ ε : ℝ) (hε : 0 < ε) (f : ℝ → TOVState)
    (hinit : (f r₀).1 = r₀)
    (hode : ∀ r ∈ Ioo (r₀ - ε) (r₀ + ε), HasDerivAt f (tovField κ χ mf G c hp (f r)) r) :
    ∀ r ∈ Ioo (r₀ - ε) (r₀ + ε), (f r).1 = r := by
  apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
  · intro r hr
    exact (hode r hr).hasFDerivAt.fst.differentiableAt.differentiableWithinAt
  · exact differentiable_id.differentiableOn
  · intro r hr
    have hh : HasDerivAt (fun t => (f t).1) 1 r := by
      convert (hode r hr).hasFDerivAt.fst.hasDerivAt using 1 <;> try rfl
      simp [tovField]
    change deriv (fun t => (f t).1) r = deriv id r
    rw [hh.deriv, (hasDerivAt_id r).deriv]
  · exact ⟨by linarith, by linarith⟩
  · exact hinit

/-- Every physical interior state has a neighborhood within the physical domain. -/
theorem tovDomain_mem_nhds (κ G c : ℝ) (hc : c ≠ 0) (p : TOVState)
    (hpar : p ∈ tovDomain κ G c) : tovDomain κ G c ∈ 𝓝 p := by
  have hr : ContinuousAt (fun q : TOVState => q.1) p := continuous_fst.continuousAt
  have hm : ContinuousAt (fun q : TOVState => q.2.1) p :=
    (continuous_fst.comp continuous_snd).continuousAt
  have hu : ContinuousAt (fun q : TOVState => q.2.2) p :=
    (continuous_snd.comp continuous_snd).continuousAt
  have hx : ContinuousAt (fun q : TOVState => compactnessRatio G c q.1 q.2.1) p :=
    (continuousAt_const.mul hm).div (hr.mul continuousAt_const)
      (mul_ne_zero (ne_of_gt hpar.1) (pow_ne_zero 2 hc))
  have huphys := hu.tendsto.eventually ((isOpen_kineticDomain κ).mem_nhds hpar.2.2.1)
  filter_upwards [hr.tendsto.eventually_const_lt hpar.1,
    hm.tendsto.eventually_const_lt hpar.2.1, huphys,
    hx.tendsto.eventually_lt_const hpar.2.2.2] with q hqr hqm hqu hqx
  exact ⟨hqr, hqm, hqu, hqx⟩

/-- Interior existence with radius identity and preservation of all physical
inequalities, available for restarting the regular-center branch. -/
theorem exists_tov_interior_physical (κ χ mf G c hp r₀ m₀ u₀ : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hc : c ≠ 0)
    (hinit : (r₀, (m₀, u₀)) ∈ tovDomain κ G c) :
    ∃ f : ℝ → TOVState, f r₀ = (r₀, (m₀, u₀)) ∧
      ∃ ε > 0, ∀ r ∈ Ioo (r₀ - ε) (r₀ + ε),
        HasDerivAt f (tovField κ χ mf G c hp (f r)) r ∧
          (f r).1 = r ∧ f r ∈ tovDomain κ G c := by
  obtain ⟨f, hf, ε, hε, hode⟩ := exists_tov_interior κ χ mf G c hp r₀ m₀ u₀ hκ hχ hc hinit
  have hmid : r₀ ∈ Ioo (r₀ - ε) (r₀ + ε) := ⟨by linarith, by linarith⟩
  have hpar : f r₀ ∈ tovDomain κ G c := by rw [hf]; exact hinit
  have hphys := (hode r₀ hmid).continuousAt.tendsto.eventually
    (tovDomain_mem_nhds κ G c hc _ hpar)
  obtain ⟨δ, hδ, hδphys⟩ := Metric.eventually_nhds_iff.mp hphys
  have hrad := tov_radius_eq κ χ mf G c hp r₀ ε hε f (congrArg Prod.fst hf) hode
  refine ⟨f, hf, min ε δ, lt_min hε hδ, ?_⟩
  intro r hr
  have hrε : r ∈ Ioo (r₀ - ε) (r₀ + ε) :=
    ⟨by linarith [hr.1, min_le_left ε δ], by linarith [hr.2, min_le_left ε δ]⟩
  refine ⟨hode r hrε, hrad r hrε, hδphys ?_⟩
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith [hr.1, min_le_right ε δ], by linarith [hr.2, min_le_right ε δ]⟩

/-! ### A contraction construction at the regular center -/

open scoped NNReal

abbrev CenterInterval := Icc (0 : ℝ) 1
abbrev CenterCurve := C(CenterInterval, ℝ)

/-- A globally bounded Lipschitz extension of (scaled density, scaled pressure,
reciprocal β). The exact kinetic EOS supplies one by clipping its parameter
inside a compact physical interval, as proved below. -/
structure CenterEOS where
  values : ℝ → TOVState
  L : ℝ≥0
  M : ℝ
  M_pos : 0 < M
  lipschitz : LipschitzWith L values
  bound : ∀ u, ‖values u‖ ≤ M

def CenterEOS.rho (E : CenterEOS) (u : ℝ) : ℝ := (E.values u).1
def CenterEOS.press (E : CenterEOS) (u : ℝ) : ℝ := (E.values u).2.1
def CenterEOS.invBeta (E : CenterEOS) (u : ℝ) : ℝ := (E.values u).2.2

def centerExtend (f : CenterCurve) (x : ℝ) : ℝ := f (projIcc 0 1 (by norm_num) x)

theorem continuous_centerExtend (f : CenterCurve) : Continuous (centerExtend f) :=
  f.continuous.comp continuous_projIcc

theorem centerExtend_of_mem (f : CenterCurve) (x : ℝ) (hx : x ∈ CenterInterval) :
    centerExtend f x = f ⟨x, hx⟩ := by simp [centerExtend, projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hx]

theorem centerExtend_dist_le (f g : CenterCurve) (x : ℝ) :
    |centerExtend f x - centerExtend g x| ≤ dist f g := by
  simpa only [centerExtend, Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := f) (g := g) (projIcc 0 1 (by norm_num) x)

theorem CenterEOS.rho_bound (E : CenterEOS) (u : ℝ) : |E.rho u| ≤ E.M :=
  (norm_fst_le (E.values u)).trans (E.bound u)

theorem CenterEOS.press_bound (E : CenterEOS) (u : ℝ) : |E.press u| ≤ E.M :=
  (norm_fst_le (E.values u).2).trans ((norm_snd_le (E.values u)).trans (E.bound u))

theorem CenterEOS.invBeta_bound (E : CenterEOS) (u : ℝ) : |E.invBeta u| ≤ E.M :=
  (norm_snd_le (E.values u).2).trans ((norm_snd_le (E.values u)).trans (E.bound u))

theorem CenterEOS.rho_continuous (E : CenterEOS) : Continuous E.rho := E.lipschitz.continuous.fst

theorem CenterEOS.press_continuous (E : CenterEOS) : Continuous E.press := E.lipschitz.continuous.snd.fst

theorem CenterEOS.invBeta_continuous (E : CenterEOS) : Continuous E.invBeta := E.lipschitz.continuous.snd.snd

theorem CenterEOS.rho_lip (E : CenterEOS) (u v : ℝ) :
    |E.rho u - E.rho v| ≤ E.L * |u - v| := by
  simpa only [CenterEOS.rho, Real.dist_eq, one_mul, NNReal.coe_one, Function.comp_def] using (LipschitzWith.prod_fst.comp E.lipschitz).dist_le_mul u v

theorem CenterEOS.press_lip (E : CenterEOS) (u v : ℝ) :
    |E.press u - E.press v| ≤ E.L * |u - v| := by
  simpa only [CenterEOS.press, Real.dist_eq, one_mul, NNReal.coe_one, Function.comp_def] using (LipschitzWith.prod_fst.comp (LipschitzWith.prod_snd.comp E.lipschitz)).dist_le_mul u v

theorem CenterEOS.invBeta_lip (E : CenterEOS) (u v : ℝ) :
    |E.invBeta u - E.invBeta v| ≤ E.L * |u - v| := by
  simpa only [CenterEOS.invBeta, Real.dist_eq, one_mul, NNReal.coe_one, Function.comp_def] using (LipschitzWith.prod_snd.comp (LipschitzWith.prod_snd.comp E.lipschitz)).dist_le_mul u v

/-- Rescaled mass average: μ(r)/r³ = ∫₀¹t²D(u(rt))dt. -/
def centerAverage (E : CenterEOS) (f : CenterCurve) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ 2 * E.rho (centerExtend f (x * t))

theorem continuous_centerAverage (E : CenterEOS) (f : CenterCurve) : Continuous (centerAverage E f) := by
  have hc : Continuous (fun p : ℝ × ℝ => p.2 ^ 2 * E.rho (centerExtend f (p.1 * p.2))) :=
    (continuous_snd.pow 2).mul (E.rho_continuous.comp ((continuous_centerExtend f).comp (continuous_fst.mul continuous_snd)))
  have hi := continuous_parametric_integral_of_continuous (μ := volume) (f := fun x t : ℝ => t ^ 2 * E.rho (centerExtend f (x * t))) hc (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  change Continuous (fun x => ∫ t in (0 : ℝ)..1, t ^ 2 * E.rho (centerExtend f (x * t)))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Icc_eq_integral_Ioc] using hi

theorem centerAverage_bound (E : CenterEOS) (f : CenterCurve) (x : ℝ) :
    |centerAverage E f x| ≤ E.M := by
  have hb : ∀ t ∈ uIoc (0 : ℝ) 1, ‖t ^ 2 * E.rho (centerExtend f (x * t))‖ ≤ E.M := by
    intro t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    exact (mul_le_mul_of_nonneg_left (E.rho_bound _) (sq_nonneg t)).trans (by nlinarith [E.M_pos])
  simpa only [centerAverage, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb

theorem centerAverage_lip (E : CenterEOS) (f g : CenterCurve) (x : ℝ) :
    |centerAverage E f x - centerAverage E g x| ≤ E.L * dist f g := by
  have hf : IntervalIntegrable (fun t => t ^ 2 * E.rho (centerExtend f (x * t))) volume 0 1 := ((continuous_id.pow 2).mul (E.rho_continuous.comp ((continuous_centerExtend f).comp (continuous_const.mul continuous_id)))).intervalIntegrable (μ := volume) 0 1
  have hg : IntervalIntegrable (fun t => t ^ 2 * E.rho (centerExtend g (x * t))) volume 0 1 := ((continuous_id.pow 2).mul (E.rho_continuous.comp ((continuous_centerExtend g).comp (continuous_const.mul continuous_id)))).intervalIntegrable (μ := volume) 0 1
  rw [centerAverage, centerAverage, ← intervalIntegral.integral_sub hf hg]
  have hb : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖t ^ 2 * E.rho (centerExtend f (x * t)) - t ^ 2 * E.rho (centerExtend g (x * t))‖ ≤ E.L * dist f g := by
    intro t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)]
    have hh := (E.rho_lip (centerExtend f (x * t)) (centerExtend g (x * t))).trans
      (mul_le_mul_of_nonneg_left (centerExtend_dist_le f g _) E.L.2)
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg t)).trans
      (by
        have hn : 0 ≤ (E.L : ℝ) * dist f g := mul_nonneg E.L.2 dist_nonneg
        nlinarith [mul_nonneg (sub_nonneg.mpr ht2) hn])
  simpa only [centerAverage, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb

theorem inverse_difference_half_bound (a b : ℝ) (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) :
    |1 / a - 1 / b| ≤ 4 * |a - b| := by
  have hap : 0 < a := by linarith
  have hbp : 0 < b := by linarith
  have hid : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  rw [hid, abs_div, abs_sub_comm b a, abs_of_pos (mul_pos hap hbp)]
  apply (div_le_iff₀ (mul_pos hap hbp)).mpr
  have hab : 1 / 4 ≤ a * b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  nlinarith [mul_nonneg (abs_nonneg (a - b)) (sub_nonneg.mpr hab)]

theorem product_difference_bound (a b c d : ℝ) :
    |a * b - c * d| ≤ |a| * |b - d| + |d| * |a - c| := by
  have he : a * b - c * d = a * (b - d) + d * (a - c) := by ring
  rw [he]
  exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])

def centerDenominator (E : CenterEOS) (sRad : ℝ) (f : CenterCurve) (x : ℝ) : ℝ :=
  max (1 / 2 : ℝ) (1 - 2 * sRad * x ^ 2 * centerAverage E f x)

def centerKernel (E : CenterEOS) (sRad : ℝ) (f : CenterCurve) (x : ℝ) : ℝ :=
  -(E.invBeta (centerExtend f x) * (centerAverage E f x + E.press (centerExtend f x))) /
    centerDenominator E sRad f x

theorem centerDenominator_ge (E : CenterEOS) (sRad : ℝ) (f : CenterCurve) (x : ℝ) :
    1 / 2 ≤ centerDenominator E sRad f x := le_max_left _ _

theorem centerDenominator_pos (E : CenterEOS) (sRad : ℝ) (f : CenterCurve) (x : ℝ) :
    0 < centerDenominator E sRad f x := lt_of_lt_of_le (by norm_num) (centerDenominator_ge E sRad f x)

theorem continuous_centerDenominator (E : CenterEOS) (sRad : ℝ) (f : CenterCurve) :
    Continuous (centerDenominator E sRad f) :=
  continuous_const.max (continuous_const.sub
    ((continuous_const.mul (continuous_id.pow 2)).mul (continuous_centerAverage E f)))

theorem continuous_centerKernel (E : CenterEOS) (sRad : ℝ) (f : CenterCurve) :
    Continuous (centerKernel E sRad f) :=
  (((E.invBeta_continuous.comp (continuous_centerExtend f)).mul
    ((continuous_centerAverage E f).add (E.press_continuous.comp (continuous_centerExtend f)))).neg).div
    (continuous_centerDenominator E sRad f) (fun x => ne_of_gt (centerDenominator_pos E sRad f x))

theorem centerKernel_bound (E : CenterEOS) (sRad : ℝ) (f : CenterCurve) (x : ℝ) :
    |centerKernel E sRad f x| ≤ 4 * E.M ^ 2 := by
  have hN : |E.invBeta (centerExtend f x) * (centerAverage E f x + E.press (centerExtend f x))| ≤ 2 * E.M ^ 2 := by
    rw [abs_mul]
    have hS : |centerAverage E f x + E.press (centerExtend f x)| ≤ 2 * E.M :=
      (abs_add_le _ _).trans (by linarith [centerAverage_bound E f x, E.press_bound (centerExtend f x)])
    exact (mul_le_mul (E.invBeta_bound _) hS (abs_nonneg _) E.M_pos.le).trans_eq (by ring)
  unfold centerKernel
  rw [abs_div, abs_neg, abs_of_pos (centerDenominator_pos E sRad f x)]
  apply (div_le_iff₀ (centerDenominator_pos E sRad f x)).mpr
  have hh := centerDenominator_ge E sRad f x
  nlinarith [mul_nonneg (sq_nonneg E.M) (sub_nonneg.mpr hh)]

theorem centerDenominator_lip (E : CenterEOS) (sRad : ℝ) (hsRad : 0 ≤ sRad) (f g : CenterCurve)
    (x : ℝ) (hx : x ∈ CenterInterval) :
    |centerDenominator E sRad f x - centerDenominator E sRad g x| ≤ 2 * sRad * E.L * dist f g := by
  have hmax := (LipschitzWith.id.const_max (1 / 2 : ℝ)).dist_le_mul
    (1 - 2 * sRad * x ^ 2 * centerAverage E f x) (1 - 2 * sRad * x ^ 2 * centerAverage E g x)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hmax
  have he : (1 - 2 * sRad * x ^ 2 * centerAverage E f x) - (1 - 2 * sRad * x ^ 2 * centerAverage E g x) =
      -(2 * sRad * x ^ 2) * (centerAverage E f x - centerAverage E g x) := by ring
  apply hmax.trans
  rw [he, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * sRad * x ^ 2)]
  have ht2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  calc
    2 * sRad * x ^ 2 * |centerAverage E f x - centerAverage E g x| ≤
        2 * sRad * x ^ 2 * (E.L * dist f g) := mul_le_mul_of_nonneg_left (centerAverage_lip E f g x) (by positivity)
    _ ≤ 2 * sRad * (E.L * dist f g) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg E.L.2 dist_nonneg)
    _ = 2 * sRad * E.L * dist f g := by ring

theorem centerKernel_lip (E : CenterEOS) (sRad : ℝ) (hsRad : 0 ≤ sRad) (hsRad1 : sRad ≤ 1)
    (f g : CenterCurve) (x : ℝ) (hx : x ∈ CenterInterval) :
    |centerKernel E sRad f x - centerKernel E sRad g x| ≤
      (8 * E.M * E.L + 16 * E.M ^ 2 * E.L) * dist f g := by
  have hM := E.M_pos
  let bf := E.invBeta (centerExtend f x)
  let bg := E.invBeta (centerExtend g x)
  let sf := centerAverage E f x + E.press (centerExtend f x)
  let sg := centerAverage E g x + E.press (centerExtend g x)
  let qf := centerDenominator E sRad f x
  let qg := centerDenominator E sRad g x
  have hb : |bf - bg| ≤ E.L * dist f g := (E.invBeta_lip _ _).trans
    (mul_le_mul_of_nonneg_left (centerExtend_dist_le f g x) E.L.2)
  have hs : |sf - sg| ≤ 2 * E.L * dist f g := by
    have he : sf - sg = (centerAverage E f x - centerAverage E g x) +
        (E.press (centerExtend f x) - E.press (centerExtend g x)) := by dsimp [sf, sg]; ring
    rw [he]
    apply (abs_add_le _ _).trans
    have hp := (E.press_lip (centerExtend f x) (centerExtend g x)).trans
      (mul_le_mul_of_nonneg_left (centerExtend_dist_le f g x) E.L.2)
    linarith [centerAverage_lip E f g x]
  have hbf : |bf| ≤ E.M := E.invBeta_bound _
  have hbg : |bg| ≤ E.M := E.invBeta_bound _
  have hsf : |sf| ≤ 2 * E.M := (abs_add_le _ _).trans (by linarith [centerAverage_bound E f x, E.press_bound (centerExtend f x)])
  have hsg : |sg| ≤ 2 * E.M := (abs_add_le _ _).trans (by linarith [centerAverage_bound E g x, E.press_bound (centerExtend g x)])
  have hN : |bf * sf - bg * sg| ≤ 4 * E.M * E.L * dist f g := by
    apply (product_difference_bound bf sf bg sg).trans
    have hh1 := mul_le_mul hbf hs (abs_nonneg _) E.M_pos.le
    have hh2 := mul_le_mul hsg hb (abs_nonneg _) (by positivity : 0 ≤ 2 * E.M)
    nlinarith
  have hNg : |bg * sg| ≤ 2 * E.M ^ 2 := by
    rw [abs_mul]
    have hh := mul_le_mul hbg hsg (abs_nonneg _) E.M_pos.le
    nlinarith
  have hqi : |1 / qf - 1 / qg| ≤ 8 * sRad * E.L * dist f g := by
    have hh := inverse_difference_half_bound qf qg (centerDenominator_ge E sRad f x) (centerDenominator_ge E sRad g x)
    have hq := centerDenominator_lip E sRad hsRad f g x hx
    nlinarith
  have hqf : |1 / qf| ≤ 2 := by
    rw [abs_of_pos (div_pos (by norm_num) (centerDenominator_pos E sRad f x))]
    apply (div_le_iff₀ (centerDenominator_pos E sRad f x)).mpr
    linarith [centerDenominator_ge E sRad f x]
  have he : centerKernel E sRad f x - centerKernel E sRad g x =
      -((bf * sf - bg * sg) * (1 / qf) + (bg * sg) * (1 / qf - 1 / qg)) := by
    dsimp [bf, bg, sf, sg, qf, qg, centerKernel]
    ring
  rw [he, abs_neg]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul]
  have hh1 := mul_le_mul hN hqf (abs_nonneg _) (by positivity : 0 ≤ 4 * E.M * E.L * dist f g)
  have hh2 := mul_le_mul hNg hqi (abs_nonneg _) (by positivity : 0 ≤ 2 * E.M ^ 2)
  have hlam := mul_le_mul_of_nonneg_right hsRad1 (by positivity : 0 ≤ 16 * E.M ^ 2 * E.L * dist f g)
  nlinarith

def centerPrimitive (E : CenterEOS) (sRad uc : ℝ) (f : CenterCurve) (x : ℝ) : ℝ :=
  uc + sRad * ∫ t in (0 : ℝ)..x, t * centerKernel E sRad f t

theorem continuous_centerPrimitive (E : CenterEOS) (sRad uc : ℝ) (f : CenterCurve) :
    Continuous (centerPrimitive E sRad uc f) :=
  continuous_const.add (continuous_const.mul
    (intervalIntegral.continuous_primitive (fun a b =>
      (continuous_id.mul (continuous_centerKernel E sRad f)).intervalIntegrable a b) 0))

/-- Picard map for the center potential on a fixed unit interval. -/
def centerPicard (E : CenterEOS) (sRad uc : ℝ) (f : CenterCurve) : CenterCurve :=
  ⟨fun x => centerPrimitive E sRad uc f x, (continuous_centerPrimitive E sRad uc f).comp continuous_subtype_val⟩

theorem centerPrimitive_at_zero (E : CenterEOS) (sRad uc : ℝ) (f : CenterCurve) :
    centerPrimitive E sRad uc f 0 = uc := by simp [centerPrimitive]

theorem hasDerivAt_centerPrimitive (E : CenterEOS) (sRad uc : ℝ) (f : CenterCurve) (x : ℝ) :
    HasDerivAt (centerPrimitive E sRad uc f) (sRad * x * centerKernel E sRad f x) x := by
  have hc := continuous_id.mul (continuous_centerKernel E sRad f)
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (μ := volume) 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert (hi.const_mul sRad).const_add uc using 1 <;> try rfl
  simp only [id_eq, Pi.mul_apply]
  ring

theorem centerPicard_bound (E : CenterEOS) (sRad uc : ℝ) (hsRad : 0 ≤ sRad)
    (f : CenterCurve) (x : CenterInterval) :
    |centerPicard E sRad uc f x - uc| ≤ 4 * sRad * E.M ^ 2 := by
  have hb : ∀ t ∈ uIoc (0 : ℝ) x.1, ‖t * centerKernel E sRad f t‖ ≤ 4 * E.M ^ 2 := by
    intro t ht
    rw [uIoc_of_le x.2.1] at ht
    have ht1 : t ≤ 1 := ht.2.trans x.2.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht.1]
    calc
      t * |centerKernel E sRad f t| ≤ t * (4 * E.M ^ 2) :=
        mul_le_mul_of_nonneg_left (centerKernel_bound E sRad f t) ht.1.le
      _ ≤ 4 * E.M ^ 2 := by nlinarith [sq_nonneg E.M]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg x.2.1] at hh
  change |(uc + sRad * ∫ t in (0 : ℝ)..x.1, t * centerKernel E sRad f t) - uc| ≤ _
  rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hsRad]
  have hi := mul_le_mul_of_nonneg_left hh hsRad
  have hx := mul_le_mul_of_nonneg_left x.2.2 (by positivity : 0 ≤ 4 * sRad * E.M ^ 2)
  nlinarith

def centerKernelLip (E : CenterEOS) : ℝ := 8 * E.M * E.L + 16 * E.M ^ 2 * E.L

theorem centerKernelLip_nonneg (E : CenterEOS) : 0 ≤ centerKernelLip E := by
  unfold centerKernelLip
  have hm := E.M_pos
  positivity

theorem centerPicard_lip (E : CenterEOS) (sRad uc : ℝ) (hsRad : 0 ≤ sRad) (hsRad1 : sRad ≤ 1)
    (f g : CenterCurve) :
    dist (centerPicard E sRad uc f) (centerPicard E sRad uc g) ≤ sRad * centerKernelLip E * dist f g := by
  have hK := centerKernelLip_nonneg E
  apply (ContinuousMap.dist_le (mul_nonneg (mul_nonneg hsRad hK) dist_nonneg)).mpr
  intro x
  have hf : IntervalIntegrable (fun t => t * centerKernel E sRad f t) volume 0 x.1 := (continuous_id.mul (continuous_centerKernel E sRad f)).intervalIntegrable (μ := volume) 0 x.1
  have hg : IntervalIntegrable (fun t => t * centerKernel E sRad g t) volume 0 x.1 := (continuous_id.mul (continuous_centerKernel E sRad g)).intervalIntegrable (μ := volume) 0 x.1
  have hb : ∀ t ∈ uIoc (0 : ℝ) x.1,
      ‖t * centerKernel E sRad f t - t * centerKernel E sRad g t‖ ≤ centerKernelLip E * dist f g := by
    intro t ht
    rw [uIoc_of_le x.2.1] at ht
    have ht1 : t ≤ 1 := ht.2.trans x.2.2
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos ht.1]
    have hk := centerKernel_lip E sRad hsRad hsRad1 f g t ⟨ht.1.le, ht1⟩
    have hh := mul_le_mul_of_nonneg_left hk ht.1.le
    exact hh.trans (by
      change t * (centerKernelLip E * dist f g) ≤ _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (mul_nonneg (centerKernelLip_nonneg E) dist_nonneg))
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg x.2.1] at hh
  change |(uc + sRad * ∫ t in (0 : ℝ)..x.1, t * centerKernel E sRad f t) -
    (uc + sRad * ∫ t in (0 : ℝ)..x.1, t * centerKernel E sRad g t)| ≤ _
  rw [add_sub_add_left_eq_sub, ← mul_sub, ← intervalIntegral.integral_sub hf hg, abs_mul, abs_of_nonneg hsRad]
  have hi := mul_le_mul_of_nonneg_left hh hsRad
  have hx := mul_le_mul_of_nonneg_left x.2.2
    (mul_nonneg (mul_nonneg hsRad (centerKernelLip_nonneg E)) (dist_nonneg (x := f) (y := g)))
  nlinarith

/-- Genuine Banach fixed-point construction, with no existence hypothesis. -/
theorem exists_center_fixedPoint (E : CenterEOS) (sRad uc : ℝ) (hsRad : 0 ≤ sRad)
    (hsRad1 : sRad ≤ 1) (hcontract : sRad * centerKernelLip E < 1) :
    ∃ f : CenterCurve, centerPicard E sRad uc f = f := by
  let K : ℝ≥0 := ⟨sRad * centerKernelLip E, mul_nonneg hsRad (centerKernelLip_nonneg E)⟩
  have hK : ContractingWith K (centerPicard E sRad uc) := by
    constructor
    · exact hcontract
    · apply LipschitzWith.of_dist_le_mul
      exact centerPicard_lip E sRad uc hsRad hsRad1
  exact ⟨hK.fixedPoint _, hK.fixedPoint_isFixedPt⟩

/-- The exact EOS in geometrized units: D=4πGρ/c², Q=4πGΠ/c²,
and β⁻¹=(1−κu)/κ. -/
def scaledKineticValues (κ χ mf G c hp u : ℝ) : TOVState :=
  (4 * Real.pi * G / c ^ 2 * densityEnergy κ χ u mf c hp,
    (4 * Real.pi * G / c ^ 2 * pressureMass κ χ u mf c hp, (1 - κ * u) / κ))

theorem contDiffAt_scaledKineticValues (κ χ mf G c hp u : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hu : u ∈ kineticDomain κ) :
    ContDiffAt ℝ 1 (scaledKineticValues κ χ mf G c hp) u := by
  have hρ := (contDiffOn_densityEnergy κ χ mf c hp hκ hχ).contDiffAt ((isOpen_kineticDomain κ).mem_nhds hu)
  have hP := (contDiffOn_pressureMass κ χ mf c hp hκ hχ).contDiffAt ((isOpen_kineticDomain κ).mem_nhds hu)
  exact (contDiffAt_const.mul hρ).prodMk ((contDiffAt_const.mul hP).prodMk
    ((contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).div_const κ))

/-- The bounded globally Lipschitz auxiliary EOS is constructed from the actual
kinetic integrals, and agrees with them near the prescribed central potential. -/
theorem exists_centerEOS (κ χ mf G c hp uc : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (huc : uc ∈ kineticDomain κ) :
    ∃ E : CenterEOS, ∃ d > 0,
      (∀ u ∈ Icc (uc - d) (uc + d), u ∈ kineticDomain κ) ∧
      (∀ u ∈ Icc (uc - d) (uc + d), E.values u = scaledKineticValues κ χ mf G c hp u) := by
  let F := scaledKineticValues κ χ mf G c hp
  obtain ⟨L, S, hS, hlip⟩ := (contDiffAt_scaledKineticValues κ χ mf G c hp uc hκ hχ huc).exists_lipschitzOnWith
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨ε, hε, hphysical⟩ := physical_parameter_rectangle κ uc hκ huc
  let d := min R ε / 2
  have hd : 0 < d := half_pos (lt_min hR hε)
  have hdR : d < R := by dsimp [d]; linarith [min_le_left R ε]
  have hdε : d ≤ ε := by dsimp [d]; linarith [min_le_right R ε]
  have hab : uc - d ≤ uc + d := by linarith
  let clip : ℝ → ℝ := fun u => (projIcc (uc - d) (uc + d) hab u : ℝ)
  have hclip : ∀ u, clip u ∈ Icc (uc - d) (uc + d) := fun u => (projIcc (uc - d) (uc + d) hab u).2
  have hnear : ∀ u ∈ Icc (uc - d) (uc + d), u ∈ S := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hh : |u - uc| ≤ d := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    exact hh.trans_lt hdR
  have huS : uc ∈ S := hnear uc ⟨by linarith, by linarith⟩
  have hLip : LipschitzWith L (fun u => F (clip u)) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hh := hlip.dist_le_mul (clip u) (hnear _ (hclip u)) (clip v) (hnear _ (hclip v))
    have hp := (LipschitzWith.projIcc hab).dist_le_mul u v
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq] at hp
    exact hh.trans (mul_le_mul_of_nonneg_left hp L.2)
  have hBound : ∀ u, ‖F (clip u)‖ ≤ ‖F uc‖ + L * d + 1 := by
    intro u
    have hh : dist (clip u) uc ≤ d := by
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith [(hclip u).1], by linarith [(hclip u).2]⟩
    have hF := (hlip.dist_le_mul (clip u) (hnear _ (hclip u)) uc huS).trans
      (mul_le_mul_of_nonneg_left hh L.2)
    have hn : ‖F (clip u)‖ ≤ dist (F (clip u)) (F uc) + ‖F uc‖ := by
      rw [dist_eq_norm]
      simpa only [sub_add_cancel] using norm_add_le (F (clip u) - F uc) (F uc)
    linarith
  let E : CenterEOS :=
    { values := fun u => F (clip u)
      L := L
      M := ‖F uc‖ + L * d + 1
      M_pos := by positivity
      lipschitz := hLip
      bound := hBound }
  refine ⟨E, d, hd, ?_, ?_⟩
  · intro u hu
    have hv : u - uc ∈ Icc (-ε) ε := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simpa only [add_sub_cancel] using hphysical (u - uc) hv
  · intro u hu
    change F (clip u) = F u
    have he : clip u = u := congrArg Subtype.val (projIcc_of_mem hab hu)
    rw [he]

/-- One strictly positive scale simultaneously gives contraction, small
central displacement, and a uniform margin from a horizon. -/
theorem exists_small_center_scale (E : CenterEOS) (d : ℝ) (hd : 0 < d) :
    ∃ sRad > 0, sRad ≤ 1 ∧ 4 * sRad * E.M ≤ 1 ∧
      4 * sRad * E.M ^ 2 ≤ d / 2 ∧ sRad * centerKernelLip E < 1 := by
  let A := centerKernelLip E + 4 * E.M + 1
  let B := 8 * E.M ^ 2 + 1
  have hM := E.M_pos
  have hK := centerKernelLip_nonneg E
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let sRad := min (1 : ℝ) (min (1 / A) (d / B)) / 2
  have hs : 0 < sRad := half_pos (lt_min (by norm_num) (lt_min (div_pos (by norm_num) hA) (div_pos hd hB)))
  have hs1 : 2 * sRad ≤ 1 := by dsimp [sRad]; linarith [min_le_left (1 : ℝ) (min (1 / A) (d / B))]
  have hsA : 2 * sRad ≤ 1 / A := by
    have hh := (min_le_right (1 : ℝ) (min (1 / A) (d / B))).trans (min_le_left (1 / A) (d / B))
    dsimp [sRad]
    linarith
  have hsB : 2 * sRad ≤ d / B := by
    have hh := (min_le_right (1 : ℝ) (min (1 / A) (d / B))).trans (min_le_right (1 / A) (d / B))
    dsimp [sRad]
    linarith
  have hmA := (le_div_iff₀ hA).mp hsA
  have hmB := (le_div_iff₀ hB).mp hsB
  dsimp [A] at hmA
  dsimp [B] at hmB
  refine ⟨sRad, hs, by linarith, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hs.le hK]
  · nlinarith [mul_nonneg hs.le (sq_nonneg E.M)]
  · nlinarith [mul_pos hs hM]

/-- All ingredients of the regular-center solution, each supplied by a proved
construction rather than an axiom or an assumed TOV trajectory. -/
structure CenterSeed (κ χ mf G c hp uc : ℝ) where
  E : CenterEOS
  d : ℝ
  d_pos : 0 < d
  sRad : ℝ
  sRad_pos : 0 < sRad
  scale_le_one : sRad ≤ 1
  horizon_margin : 4 * sRad * E.M ≤ 1
  displacement : 4 * sRad * E.M ^ 2 ≤ d / 2
  contraction : sRad * centerKernelLip E < 1
  f : CenterCurve
  fixedPoint : centerPicard E sRad uc f = f
  physical : ∀ u ∈ Icc (uc - d) (uc + d), u ∈ kineticDomain κ
  agrees : ∀ u ∈ Icc (uc - d) (uc + d), E.values u = scaledKineticValues κ χ mf G c hp u

theorem exists_centerSeed (κ χ mf G c hp uc : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (huc : uc ∈ kineticDomain κ) : Nonempty (CenterSeed κ χ mf G c hp uc) := by
  obtain ⟨E, d, hd, hphysical, hagrees⟩ := exists_centerEOS κ χ mf G c hp uc hκ hχ huc
  obtain ⟨sRad, hsRad, hs1, hhorizon, hdispl, hcontract⟩ := exists_small_center_scale E d hd
  obtain ⟨f, hfixed⟩ := exists_center_fixedPoint E sRad uc hsRad.le hs1 hcontract
  exact ⟨⟨E, d, hd, sRad, hsRad, hs1, hhorizon, hdispl, hcontract, f, hfixed, hphysical, hagrees⟩⟩

namespace CenterSeed

variable {κ χ mf G c hp uc : ℝ} (S : CenterSeed κ χ mf G c hp uc)

def radius : ℝ := Real.sqrt S.sRad

theorem radius_pos : 0 < S.radius := Real.sqrt_pos.mpr S.sRad_pos

theorem radius_sq : S.radius ^ 2 = S.sRad := Real.sq_sqrt S.sRad_pos.le

theorem potential_eq_extend (x : ℝ) (hx : x ∈ CenterInterval) :
    centerPrimitive S.E S.sRad uc S.f x = centerExtend S.f x := by
  rw [centerExtend_of_mem S.f x hx]
  exact congrArg (fun f : CenterCurve => f ⟨x, hx⟩) S.fixedPoint

theorem curve_near (x : ℝ) (hx : x ∈ CenterInterval) :
    centerExtend S.f x ∈ Icc (uc - S.d) (uc + S.d) := by
  have hb := centerPicard_bound S.E S.sRad uc S.sRad_pos.le S.f ⟨x, hx⟩
  rw [S.fixedPoint] at hb
  rw [centerExtend_of_mem S.f x hx]
  have hab := abs_le.mp (hb.trans S.displacement)
  exact ⟨by linarith [S.d_pos], by linarith [S.d_pos]⟩

def potential (r : ℝ) : ℝ := centerPrimitive S.E S.sRad uc S.f (r / S.radius)

def massGeometric (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..r, t ^ 2 * S.E.rho (centerExtend S.f (t / S.radius))

def mass (r : ℝ) : ℝ := c ^ 2 / G * S.massGeometric r

theorem continuous_potential : Continuous S.potential :=
  (continuous_centerPrimitive S.E S.sRad uc S.f).comp (continuous_id.div_const S.radius)

theorem continuous_massGeometric : Continuous S.massGeometric :=
  intervalIntegral.continuous_primitive (fun a b =>
    ((continuous_id.pow 2).mul (S.E.rho_continuous.comp
      ((continuous_centerExtend S.f).comp (continuous_id.div_const S.radius)))).intervalIntegrable a b) 0

theorem continuous_mass : Continuous S.mass := continuous_const.mul S.continuous_massGeometric

theorem potential_at_zero : S.potential 0 = uc := by
  simp [potential, centerPrimitive]

theorem mass_at_zero : S.mass 0 = 0 := by simp [mass, massGeometric]

theorem normalizedRadius_mem (r : ℝ) (hr : r ∈ Icc (0 : ℝ) S.radius) :
    r / S.radius ∈ CenterInterval :=
  ⟨div_nonneg hr.1 S.radius_pos.le, (div_le_one S.radius_pos).mpr hr.2⟩

theorem potential_eq_extend_radius (r : ℝ) (hr : r ∈ Icc (0 : ℝ) S.radius) :
    S.potential r = centerExtend S.f (r / S.radius) :=
  S.potential_eq_extend _ (S.normalizedRadius_mem r hr)

theorem potential_physical (r : ℝ) (hr : r ∈ Icc (0 : ℝ) S.radius) :
    S.potential r ∈ kineticDomain κ := by
  rw [S.potential_eq_extend_radius r hr]
  exact S.physical _ (S.curve_near _ (S.normalizedRadius_mem r hr))

theorem EOS_agrees (r : ℝ) (hr : r ∈ Icc (0 : ℝ) S.radius) :
    S.E.values (centerExtend S.f (r / S.radius)) =
      scaledKineticValues κ χ mf G c hp (S.potential r) := by
  rw [S.potential_eq_extend_radius r hr]
  exact S.agrees _ (S.curve_near _ (S.normalizedRadius_mem r hr))

theorem massGeometric_average (r : ℝ) :
    S.massGeometric r = r ^ 3 * centerAverage S.E S.f (r / S.radius) := by
  have hi := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => t ^ 2 * S.E.rho (centerExtend S.f (t / S.radius))) (a := (0 : ℝ)) (b := 1) r
  simp only [smul_eq_mul, mul_zero, mul_one] at hi
  rw [massGeometric, ← hi]
  have he : (fun t : ℝ => (r * t) ^ 2 * S.E.rho (centerExtend S.f (r * t / S.radius))) =
      (fun t : ℝ => r ^ 2 * (t ^ 2 * S.E.rho (centerExtend S.f (r / S.radius * t)))) := by
    funext t
    rw [mul_div_right_comm]
    ring
  rw [he, intervalIntegral.integral_const_mul]
  unfold centerAverage
  ring

theorem denominator_eq (x : ℝ) (hx : x ∈ CenterInterval) :
    centerDenominator S.E S.sRad S.f x = 1 - 2 * S.sRad * x ^ 2 * centerAverage S.E S.f x := by
  have hs := S.sRad_pos
  have hm := S.E.M_pos
  apply max_eq_right
  have hA := (le_abs_self (centerAverage S.E S.f x)).trans (centerAverage_bound S.E S.f x)
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have hh := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ 2 * S.sRad * x ^ 2)
  have hxM := mul_le_mul_of_nonneg_right hx2 (by positivity : 0 ≤ 2 * S.sRad * S.E.M)
  nlinarith [S.horizon_margin]

theorem compactness_identity (r : ℝ) (hG : G ≠ 0) (hc : c ≠ 0) (hr : r ≠ 0) :
    compactnessRatio G c r (S.mass r) = 2 * r ^ 2 * centerAverage S.E S.f (r / S.radius) := by
  rw [compactnessRatio, mass, S.massGeometric_average]
  field_simp


theorem horizon_margin_radius (r : ℝ) (hr : r ∈ Icc (0 : ℝ) S.radius) :
    1 / 2 ≤ 1 - 2 * r ^ 2 * centerAverage S.E S.f (r / S.radius) := by
  have hx := S.normalizedRadius_mem r hr
  have hd := centerDenominator_ge S.E S.sRad S.f (r / S.radius)
  rw [S.denominator_eq _ hx] at hd
  have he : S.sRad * (r / S.radius) ^ 2 = r ^ 2 := by
    rw [← S.radius_sq, div_pow]
    field_simp [ne_of_gt S.radius_pos]
  have he2 : 2 * S.sRad * (r / S.radius) ^ 2 = 2 * r ^ 2 := by nlinarith [he]
  rwa [he2] at hd

/-- A regular center potential has derivative zero at the center. -/
theorem hasDerivAt_potential (r : ℝ) :
    HasDerivAt S.potential ((S.sRad * (r / S.radius) * centerKernel S.E S.sRad S.f (r / S.radius)) / S.radius) r := by
  have hi := (hasDerivAt_centerPrimitive S.E S.sRad uc S.f (r / S.radius)).comp r
    ((hasDerivAt_id r).div_const S.radius)
  convert hi using 1 <;> first | rfl | (simp only [potential, Function.comp_def, id_eq, one_div, one_mul, div_eq_mul_inv] <;> ring)

/-- The constructed geometric mass is C¹, including at r=0. -/
theorem hasDerivAt_massGeometric (r : ℝ) :
    HasDerivAt S.massGeometric (r ^ 2 * S.E.rho (centerExtend S.f (r / S.radius))) r := by
  have hc := (continuous_id.pow 2).mul (S.E.rho_continuous.comp
    ((continuous_centerExtend S.f).comp (continuous_id.div_const S.radius)))
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (μ := volume) 0 r)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt


/-- The mass derivative is the physical TOV mass equation. -/
theorem hasDerivAt_mass (hG : G ≠ 0) (hc : c ≠ 0) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) S.radius) :
    HasDerivAt S.mass (4 * Real.pi * r ^ 2 * densityEnergy κ χ (S.potential r) mf c hp) r := by
  have hd := (S.hasDerivAt_massGeometric r).const_mul (c ^ 2 / G)
  have he := congrArg Prod.fst (S.EOS_agrees r hr)
  change S.E.rho (centerExtend S.f (r / S.radius)) =
    4 * Real.pi * G / c ^ 2 * densityEnergy κ χ (S.potential r) mf c hp at he
  convert hd using 1 <;> try rfl
  rw [he]
  field_simp


/-- The physical potential equation is obtained from the center fixed point,
not postulated as a hypothesis. -/
theorem hasDerivAt_potential_TOV (hκ : 0 < κ) (hG : G ≠ 0) (hc : c ≠ 0)
    (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) S.radius) :
    HasDerivAt S.potential
      (-G * (S.mass r + 4 * Real.pi * r ^ 3 * pressureMass κ χ (S.potential r) mf c hp) /
        (c ^ 2 * r ^ 2 * beta κ (S.potential r) * (1 - compactnessRatio G c r (S.mass r)))) r := by
  have hpar := S.potential_physical r ⟨hr.1.le, hr.2⟩
  have hx := S.normalizedRadius_mem r ⟨hr.1.le, hr.2⟩
  have hb : beta κ (S.potential r) ≠ 0 := ne_of_gt (div_pos hκ hpar.2)
  have hR : S.radius ≠ 0 := ne_of_gt S.radius_pos
  have hden : 1 - 2 * r ^ 2 * centerAverage S.E S.f (r / S.radius) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (S.horizon_margin_radius r ⟨hr.1.le, hr.2⟩))
  have hP := congrArg (fun q : TOVState => q.2.1) (S.EOS_agrees r ⟨hr.1.le, hr.2⟩)
  have hβ := congrArg (fun q : TOVState => q.2.2) (S.EOS_agrees r ⟨hr.1.le, hr.2⟩)
  change S.E.press (centerExtend S.f (r / S.radius)) =
    4 * Real.pi * G / c ^ 2 * pressureMass κ χ (S.potential r) mf c hp at hP
  change S.E.invBeta (centerExtend S.f (r / S.radius)) = (1 - κ * S.potential r) / κ at hβ
  convert S.hasDerivAt_potential r using 1 <;> try rfl
  rw [S.compactness_identity r hG hc (ne_of_gt hr.1)]
  unfold centerKernel
  rw [S.denominator_eq _ hx, hP, hβ]
  unfold mass
  rw [S.massGeometric_average]
  unfold beta
  rw [← S.radius_sq]
  have he : S.radius ^ 2 * (r / S.radius) ^ 2 = r ^ 2 := by field_simp
  have he2 : 2 * S.radius ^ 2 * (r / S.radius) ^ 2 = 2 * r ^ 2 := by nlinarith [he]
  rw [he2]
  generalize centerAverage S.E S.f (r / S.radius) = A at *
  have hfull : G * c ^ 2 * r ^ 2 * κ - G * c ^ 2 * r ^ 4 * A * κ * 2 ≠ 0 := by
    have heq : G * c ^ 2 * r ^ 2 * κ - G * c ^ 2 * r ^ 4 * A * κ * 2 =
        (G * c ^ 2 * r ^ 2 * κ) * (1 - 2 * r ^ 2 * A) := by ring
    rw [heq]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hG (pow_ne_zero 2 hc))
      (pow_ne_zero 2 (ne_of_gt hr.1))) (ne_of_gt hκ)) hden
  field_simp [hfull, ne_of_gt hκ, ne_of_gt hr.1, hR, hden, hG, hc, ne_of_gt hpar.2]



theorem hasDerivAt_potential_center : HasDerivAt S.potential 0 0 := by
  simpa only [zero_div, mul_zero, zero_mul] using S.hasDerivAt_potential 0

theorem horizonFree (hG : G ≠ 0) (hc : c ≠ 0) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) S.radius) : compactnessRatio G c r (S.mass r) ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hr.1 with he | he
  · rw [← he, S.mass_at_zero]
    simp [compactnessRatio]
  · rw [S.compactness_identity r hG hc (ne_of_gt he)]
    linarith [S.horizon_margin_radius r hr]

end CenterSeed

/-- Local regular-center TOV existence for every physical central potential.
The functions are constructed from a contraction; all kinetic regularity and
horizon-free properties below are conclusions of the proof. -/
theorem exists_regular_center_TOV (κ χ mf G c hp uc : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hG : G ≠ 0) (hc : c ≠ 0)
    (huc : uc ∈ kineticDomain κ) :
    ∃ R > 0, ∃ m u : ℝ → ℝ,
      Continuous m ∧ Continuous u ∧ m 0 = 0 ∧ u 0 = uc ∧ HasDerivAt u 0 0 ∧
      (∀ r ∈ Icc (0 : ℝ) R, u r ∈ kineticDomain κ ∧ compactnessRatio G c r (m r) ≤ 1 / 2) ∧
      (∀ r ∈ Icc (0 : ℝ) R, HasDerivAt m (4 * Real.pi * r ^ 2 * densityEnergy κ χ (u r) mf c hp) r) ∧
      (∀ r ∈ Ioc (0 : ℝ) R, HasDerivAt u
        (-G * (m r + 4 * Real.pi * r ^ 3 * pressureMass κ χ (u r) mf c hp) /
          (c ^ 2 * r ^ 2 * beta κ (u r) * (1 - compactnessRatio G c r (m r)))) r) := by
  obtain ⟨S⟩ := exists_centerSeed κ χ mf G c hp uc hκ hχ huc
  refine ⟨S.radius, S.radius_pos, S.mass, S.potential,
    S.continuous_mass, S.continuous_potential, S.mass_at_zero, S.potential_at_zero,
    S.hasDerivAt_potential_center, ?_, S.hasDerivAt_mass hG hc, S.hasDerivAt_potential_TOV hκ hG hc⟩
  intro r hr
  exact ⟨S.potential_physical r hr, S.horizonFree hG hc r hr⟩

/-- Positive density for the exact kinetic EOS. -/
theorem densityEnergy_pos (κ χ u mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hu : u ∈ kineticDomain κ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    0 < densityEnergy κ χ u mf c hp :=
  mul_pos (kineticConstant_pos mf c hp hmf hc hhp)
    (add_pos (momentA_pos κ χ u hκ hχ hu.1 hu.2) (momentB_pos κ χ u hκ hχ hu.1 hu.2))

theorem pressureMass_pos (κ χ u mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hu : u ∈ kineticDomain κ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    0 < pressureMass κ χ u mf c hp :=
  mul_pos (div_pos (kineticConstant_pos mf c hp hmf hc hhp) (by norm_num))
    (momentA_pos κ χ u hκ hχ hu.1 hu.2)

theorem densityEnergy_derivative_pos (κ χ u mf c hp : ℝ) (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hu : u ∈ kineticDomain κ) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    0 < kineticConstant mf c hp * beta κ u *
      (4 * momentA κ χ u + 5 * momentB κ χ u + momentC κ χ u) := by
  have hK := kineticConstant_pos mf c hp hmf hc hhp
  have hβ : 0 < beta κ u := div_pos hκ hu.2
  have hA := momentA_pos κ χ u hκ hχ hu.1 hu.2
  have hB := momentB_pos κ χ u hκ hχ hu.1 hu.2
  have hC := momentC_nonneg κ χ u hκ hχ hu.1 hu.2
  positivity

namespace CenterSeed

variable {κ χ mf G c hp uc : ℝ} (S : CenterSeed κ χ mf G c hp uc)

/-- The constructed mass is the physical mass integral, including at the center. -/
theorem mass_integral (hG : G ≠ 0) (hc : c ≠ 0) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) S.radius) :
    S.mass r = 4 * Real.pi * ∫ t in (0 : ℝ)..r, t ^ 2 * densityEnergy κ χ (S.potential t) mf c hp := by
  have he : S.massGeometric r = (4 * Real.pi * G / c ^ 2) *
      (∫ t in (0 : ℝ)..r, t ^ 2 * densityEnergy κ χ (S.potential t) mf c hp) := by
    rw [massGeometric, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun t ht => by
      rw [uIoc_of_le hr.1] at ht
      have hEOS := congrArg Prod.fst (S.EOS_agrees t ⟨ht.1.le, ht.2.trans hr.2⟩)
      change S.E.rho (centerExtend S.f (t / S.radius)) =
        4 * Real.pi * G / c ^ 2 * densityEnergy κ χ (S.potential t) mf c hp at hEOS
      rw [hEOS]
      ring)
  rw [mass, he]
  field_simp


theorem density_continuousOn (hκ : 0 < κ) (hχ : 0 ≤ χ) :
    ContinuousOn (fun r => densityEnergy κ χ (S.potential r) mf c hp) (Icc (0 : ℝ) S.radius) :=
  (contDiffOn_densityEnergy κ χ mf c hp hκ hχ).continuousOn.comp S.continuous_potential.continuousOn
    (fun r hr => S.potential_physical r hr)

/-- Every positive interior radius encloses positive mass. -/
theorem mass_pos (hκ : 0 < κ) (hχ : 0 ≤ χ) (hG : G ≠ 0)
    (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) S.radius) :
    0 < S.mass r := by
  have hrp : 0 < r := hr.1
  have hrR : r ≤ S.radius := hr.2
  rw [S.mass_integral hG (ne_of_gt hc) r ⟨hr.1.le, hr.2⟩]
  apply mul_pos (by positivity)
  apply intervalIntegral.integral_pos hr.1
    ((continuous_id.pow 2).continuousOn.mul ((S.density_continuousOn hκ hχ).mono (Icc_subset_Icc_right hr.2)))
  · intro t ht
    exact mul_nonneg (sq_nonneg t)
      (densityEnergy_pos κ χ _ mf c hp hκ hχ (S.potential_physical t ⟨ht.1.le, ht.2.trans hr.2⟩) hmf hc hhp).le
  · refine ⟨r / 2, ⟨by linarith, by linarith⟩, ?_⟩
    exact mul_pos (sq_pos_of_pos (half_pos hr.1))
      (densityEnergy_pos κ χ _ mf c hp hκ hχ (S.potential_physical _ ⟨by linarith, by linarith⟩) hmf hc hhp)

/-- The radial potential derivative is strictly negative for r>0. -/
theorem potential_derivative_neg (hκ : 0 < κ) (hχ : 0 ≤ χ) (hG : 0 < G)
    (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) S.radius) :
    deriv S.potential r < 0 := by
  have hrp : 0 < r := hr.1
  rw [(S.hasDerivAt_potential_TOV hκ (ne_of_gt hG) (ne_of_gt hc) r hr).deriv]
  have hpar := S.potential_physical r ⟨hr.1.le, hr.2⟩
  have hm := S.mass_pos hκ hχ (ne_of_gt hG) hmf hc hhp r hr
  have hP := pressureMass_pos κ χ _ mf c hp hκ hχ hpar hmf hc hhp
  have hb : 0 < beta κ (S.potential r) := div_pos hκ hpar.2
  have hx : 0 < 1 - compactnessRatio G c r (S.mass r) := by
    linarith [S.horizonFree (ne_of_gt hG) (ne_of_gt hc) r ⟨hr.1.le, hr.2⟩]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hG) (by positivity)) (by positivity)

/-- Strict decrease of physical density follows from the proved EOS derivative
and the constructed TOV potential equation. -/
theorem density_strictAntiOn (hκ : 0 < κ) (hχ : 0 ≤ χ) (hG : 0 < G)
    (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    StrictAntiOn (fun r => densityEnergy κ χ (S.potential r) mf c hp) (Icc (0 : ℝ) S.radius) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (S.density_continuousOn hκ hχ)
  intro r hr
  rw [interior_Icc] at hr
  have hpar := S.potential_physical r ⟨hr.1.le, hr.2.le⟩
  have hdu := S.hasDerivAt_potential_TOV hκ (ne_of_gt hG) (ne_of_gt hc) r ⟨hr.1, hr.2.le⟩
  have hdρ := (hasDerivAt_densityEnergy κ χ _ mf c hp hκ hχ hpar.1 hpar.2).comp r hdu
  dsimp only [Function.comp_def] at hdρ
  rw [hdρ.deriv]
  have hneg := S.potential_derivative_neg hκ hχ hG hmf hc hhp r ⟨hr.1, hr.2.le⟩
  rw [hdu.deriv] at hneg
  exact mul_neg_of_pos_of_neg
    (densityEnergy_derivative_pos κ χ _ mf c hp hκ hχ hpar hmf hc hhp) hneg

/-- The strict physical wedge follows from density decrease and the mass
integral; it is not an additional invariant-set assumption. -/
theorem mass_strict_density_bound (hκ : 0 < κ) (hχ : 0 ≤ χ) (hG : 0 < G)
    (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) S.radius) :
    (4 * Real.pi / 3) * r ^ 3 * densityEnergy κ χ (S.potential r) mf c hp < S.mass r := by
  have hrp : 0 < r := hr.1
  have hrR : r ≤ S.radius := hr.2
  have hanti := S.density_strictAntiOn hκ hχ hG hmf hc hhp
  have hd := (S.density_continuousOn hκ hχ).mono (Icc_subset_Icc_right hr.2)
  have hi : (∫ t in (0 : ℝ)..r, t ^ 2 * densityEnergy κ χ (S.potential r) mf c hp) <
      ∫ t in (0 : ℝ)..r, t ^ 2 * densityEnergy κ χ (S.potential t) mf c hp := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hr.1
      ((continuous_id.pow 2).mul continuous_const).continuousOn
      ((continuous_id.pow 2).continuousOn.mul hd)
    · intro t ht
      exact mul_le_mul_of_nonneg_left (hanti.antitoneOn ⟨ht.1.le, ht.2.trans hr.2⟩ ⟨hr.1.le, hr.2⟩ ht.2) (sq_nonneg t)
    · refine ⟨r / 2, ⟨by linarith, by linarith⟩, ?_⟩
      apply mul_lt_mul_of_pos_left
        (hanti ⟨by linarith, by linarith⟩ ⟨hr.1.le, hr.2⟩ (by linarith)) (sq_pos_of_pos (half_pos hr.1))
  rw [intervalIntegral.integral_mul_const, integral_pow] at hi
  norm_num at hi
  rw [S.mass_integral (ne_of_gt hG) (ne_of_gt hc) r ⟨hr.1.le, hr.2⟩]
  have hh := mul_lt_mul_of_pos_left hi (by positivity : (0 : ℝ) < 4 * Real.pi)
  nlinarith

end CenterSeed

namespace CenterSeed

variable {κ χ mf G c hp uc : ℝ} (S : CenterSeed κ χ mf G c hp uc)

theorem average_at_zero : centerAverage S.E S.f 0 = S.E.rho uc / 3 := by
  have he : centerExtend S.f 0 = uc := by
    simpa only [zero_div, S.potential_at_zero] using
      (S.potential_eq_extend_radius 0 ⟨le_rfl, S.radius_pos.le⟩).symm
  unfold centerAverage
  simp only [zero_mul, he]
  rw [intervalIntegral.integral_mul_const, integral_pow]
  norm_num
  ring

/-- The cubic mass expansion is proved at the center, including its coefficient. -/
theorem tendsto_mass_over_cube (hG : G ≠ 0) (hc : c ≠ 0) :
    Tendsto (fun r => S.mass r / r ^ 3) (𝓝[>] (0 : ℝ))
      (𝓝 (4 * Real.pi / 3 * densityEnergy κ χ uc mf c hp)) := by
  have hr : Tendsto (fun r : ℝ => r / S.radius) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [id_eq, zero_div] using ((continuousAt_id : ContinuousAt (fun r : ℝ => r) 0).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).div_const S.radius
  have hAvg := ((continuous_centerAverage S.E S.f).tendsto 0).comp hr
  have hlim := hAvg.const_mul (c ^ 2 / G)
  have he : (fun r => S.mass r / r ^ 3) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r => c ^ 2 / G * centerAverage S.E S.f (r / S.radius)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hne : r ≠ 0 := ne_of_gt (show 0 < r from hr)
    rw [mass, S.massGeometric_average]
    field_simp

  apply (tendsto_congr' he).mpr
  have hEOS := congrArg Prod.fst (S.EOS_agrees 0 ⟨le_rfl, S.radius_pos.le⟩)
  rw [S.potential_at_zero] at hEOS
  have hf : centerExtend S.f (0 / S.radius) = uc := by
    simpa only [S.potential_at_zero] using
      (S.potential_eq_extend_radius 0 ⟨le_rfl, S.radius_pos.le⟩).symm
  rw [hf] at hEOS
  change S.E.rho uc = 4 * Real.pi * G / c ^ 2 * densityEnergy κ χ uc mf c hp at hEOS
  rw [S.average_at_zero, hEOS] at hlim
  convert hlim using 1 <;> try rfl
  field_simp


/-- The physical pressure equation follows from the constructed potential
and the proved kinetic enthalpy identity. -/
theorem hasDerivAt_pressure_TOV (hκ : 0 < κ) (hχ : 0 ≤ χ) (hG : G ≠ 0) (hc : c ≠ 0)
    (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) S.radius) :
    HasDerivAt (fun t => pressureEnergy κ χ (S.potential t) mf c hp)
      (-G * (densityEnergy κ χ (S.potential r) mf c hp + pressureMass κ χ (S.potential r) mf c hp) *
        (S.mass r + 4 * Real.pi * r ^ 3 * pressureMass κ χ (S.potential r) mf c hp) /
        (r ^ 2 * (1 - compactnessRatio G c r (S.mass r)))) r := by
  have hpar := S.potential_physical r ⟨hr.1.le, hr.2⟩
  have hdu := S.hasDerivAt_potential_TOV hκ hG hc r hr
  have hP := hasDerivAt_pressureEnergy κ χ (S.potential r) mf c hp hκ hχ hpar.1 hpar.2
  have hβ : beta κ (S.potential r) ≠ 0 := ne_of_gt (div_pos hκ hpar.2)
  have hx : 1 - compactnessRatio G c r (S.mass r) ≠ 0 := by
    have hh := S.horizonFree hG hc r ⟨hr.1.le, hr.2⟩
    exact ne_of_gt (by linarith)
  have he : kineticConstant mf c hp * (4 * momentA κ χ (S.potential r) / 3 + momentB κ χ (S.potential r)) =
      densityEnergy κ χ (S.potential r) mf c hp + pressureMass κ χ (S.potential r) mf c hp := by
    unfold densityEnergy pressureMass
    ring
  convert hP.comp r hdu using 1 <;> try rfl
  have hcoef : c ^ 2 * kineticConstant mf c hp * beta κ (S.potential r) *
      (4 * momentA κ χ (S.potential r) / 3 + momentB κ χ (S.potential r)) =
      c ^ 2 * beta κ (S.potential r) *
        (densityEnergy κ χ (S.potential r) mf c hp + pressureMass κ χ (S.potential r) mf c hp) := by
    rw [← he]
    ring
  rw [hcoef]
  field_simp [hc, ne_of_gt hr.1, hβ, hx]

end CenterSeed

/-- A regular kinetic TOV configuration exists on a nonzero interval for every
physical central potential. Mass positivity, density decrease, and the strict
mass-density wedge are proved here, rather than assumed. A finite vacuum
surface at the outer endpoint is not asserted by this local theorem. -/
theorem exists_physical_regular_TOV (κ χ mf G c hp uc : ℝ)
    (hκ : 0 < κ) (hχ : 0 ≤ χ) (hmf : 0 < mf) (hG : 0 < G) (hc : 0 < c) (hhp : 0 < hp)
    (huc : uc ∈ kineticDomain κ) :
    ∃ R > 0, ∃ m u : ℝ → ℝ,
      Continuous m ∧ Continuous u ∧ m 0 = 0 ∧ u 0 = uc ∧ HasDerivAt u 0 0 ∧
      (∀ r ∈ Icc (0 : ℝ) R, u r ∈ kineticDomain κ ∧ compactnessRatio G c r (m r) ≤ 1 / 2) ∧
      (∀ r ∈ Icc (0 : ℝ) R, HasDerivAt m (4 * Real.pi * r ^ 2 * densityEnergy κ χ (u r) mf c hp) r) ∧
      (∀ r ∈ Ioc (0 : ℝ) R, HasDerivAt u
        (-G * (m r + 4 * Real.pi * r ^ 3 * pressureMass κ χ (u r) mf c hp) /
          (c ^ 2 * r ^ 2 * beta κ (u r) * (1 - compactnessRatio G c r (m r)))) r) ∧
      (∀ r ∈ Ioc (0 : ℝ) R, HasDerivAt (fun t => pressureEnergy κ χ (u t) mf c hp)
        (-G * (densityEnergy κ χ (u r) mf c hp + pressureMass κ χ (u r) mf c hp) *
          (m r + 4 * Real.pi * r ^ 3 * pressureMass κ χ (u r) mf c hp) /
          (r ^ 2 * (1 - compactnessRatio G c r (m r)))) r) ∧
      (∀ r ∈ Ioc (0 : ℝ) R, 0 < m r ∧
        (4 * Real.pi / 3) * r ^ 3 * densityEnergy κ χ (u r) mf c hp < m r) ∧
      StrictAntiOn (fun r => densityEnergy κ χ (u r) mf c hp) (Icc (0 : ℝ) R) ∧
      Tendsto (fun r => m r / r ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 (4 * Real.pi / 3 * densityEnergy κ χ uc mf c hp)) := by
  obtain ⟨S⟩ := exists_centerSeed κ χ mf G c hp uc hκ hχ huc
  refine ⟨S.radius, S.radius_pos, S.mass, S.potential, S.continuous_mass, S.continuous_potential,
    S.mass_at_zero, S.potential_at_zero, S.hasDerivAt_potential_center, ?_,
    S.hasDerivAt_mass (ne_of_gt hG) (ne_of_gt hc), S.hasDerivAt_potential_TOV hκ (ne_of_gt hG) (ne_of_gt hc),
    S.hasDerivAt_pressure_TOV hκ hχ (ne_of_gt hG) (ne_of_gt hc), ?_,
    S.density_strictAntiOn hκ hχ hG hmf hc hhp, S.tendsto_mass_over_cube (ne_of_gt hG) (ne_of_gt hc)⟩
  · intro r hr
    exact ⟨S.potential_physical r hr, S.horizonFree (ne_of_gt hG) (ne_of_gt hc) r hr⟩
  · intro r hr
    exact ⟨S.mass_pos hκ hχ (ne_of_gt hG) hmf hc hhp r hr,
      S.mass_strict_density_bound hκ hχ hG hmf hc hhp r hr⟩


/-- The phase density variable used by the filled-barrier argument. -/
def phaseDensity (κ χ mf G c hp : ℝ) (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  8 * Real.pi * G * r ^ 2 * densityEnergy κ χ (u r) mf c hp / c ^ 2

namespace CenterSeed

variable {κ χ mf G c hp uc : ℝ} (S : CenterSeed κ χ mf G c hp uc)

/-- The constructed trajectory satisfies the paper's strict wedge 0<y<3x. -/
theorem phase_wedge (hκ : 0 < κ) (hχ : 0 ≤ χ) (hG : 0 < G)
    (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp)
    (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) S.radius) :
    0 < phaseDensity κ χ mf G c hp S.potential r ∧
      phaseDensity κ χ mf G c hp S.potential r < 3 * compactnessRatio G c r (S.mass r) := by
  have hpar := S.potential_physical r ⟨hr.1.le, hr.2⟩
  have hρ := densityEnergy_pos κ χ (S.potential r) mf c hp hκ hχ hpar hmf hc hhp
  have hrp : 0 < r := hr.1
  have hm := S.mass_strict_density_bound hκ hχ hG hmf hc hhp r hr
  constructor
  · unfold phaseDensity
    positivity
  · unfold phaseDensity compactnessRatio
    rw [← mul_div_assoc]
    apply (div_lt_div_iff₀ (sq_pos_of_pos hc) (mul_pos hrp (sq_pos_of_pos hc))).mpr
    have hi := mul_lt_mul_of_pos_left hm (by positivity : 0 < 6 * G * c ^ 2)
    nlinarith

/-- The compactness starts quadratically with the regular-center coefficient. -/
theorem tendsto_compactness_over_square (hG : G ≠ 0) (hc : c ≠ 0) :
    Tendsto (fun r => compactnessRatio G c r (S.mass r) / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (8 * Real.pi * G / (3 * c ^ 2) * densityEnergy κ χ uc mf c hp)) := by
  have ht := (S.tendsto_mass_over_cube hG hc).const_mul (2 * G / c ^ 2)
  have he : (fun r => compactnessRatio G c r (S.mass r) / r ^ 2) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r => 2 * G / c ^ 2 * (S.mass r / r ^ 3)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hn : r ≠ 0 := ne_of_gt (show 0 < r from hr)
    unfold compactnessRatio
    field_simp [hn, hc] <;> ring <;> simp
  apply (tendsto_congr' he).mpr
  convert ht using 1 <;> ring

theorem tendsto_phaseDensity_over_square (hκ : 0 < κ) (hχ : 0 ≤ χ) (hc : c ≠ 0) :
    Tendsto (fun r => phaseDensity κ χ mf G c hp S.potential r / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (8 * Real.pi * G / c ^ 2 * densityEnergy κ χ uc mf c hp)) := by
  have hpar := S.potential_physical 0 ⟨le_rfl, S.radius_pos.le⟩
  rw [S.potential_at_zero] at hpar
  have hρ := (hasDerivAt_densityEnergy κ χ uc mf c hp hκ hχ hpar.1 hpar.2).continuousAt
  have ht := (hρ.tendsto.comp (by simpa only [S.potential_at_zero] using
    S.continuous_potential.continuousAt.tendsto (x := (0 : ℝ)))).const_mul (8 * Real.pi * G / c ^ 2)
  have he : (fun r => phaseDensity κ χ mf G c hp S.potential r / r ^ 2) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r => 8 * Real.pi * G / c ^ 2 * densityEnergy κ χ (S.potential r) mf c hp) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hn : r ≠ 0 := ne_of_gt (show 0 < r from hr)
    unfold phaseDensity
    field_simp

  exact (tendsto_congr' he).mpr (ht.mono_left nhdsWithin_le_nhds)

/-- The trajectory has the center tangent y/x -> 3 used in phase-plane estimates. -/
theorem tendsto_phaseDensity_div_compactness (hκ : 0 < κ) (hχ : 0 ≤ χ)
    (hG : 0 < G) (hmf : 0 < mf) (hc : 0 < c) (hhp : 0 < hp) :
    Tendsto (fun r => phaseDensity κ χ mf G c hp S.potential r /
      compactnessRatio G c r (S.mass r)) (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℝ)) := by
  have hpar := S.potential_physical 0 ⟨le_rfl, S.radius_pos.le⟩
  rw [S.potential_at_zero] at hpar
  have hρ := densityEnergy_pos κ χ uc mf c hp hκ hχ hpar hmf hc hhp
  have hn : 8 * Real.pi * G / (3 * c ^ 2) * densityEnergy κ χ uc mf c hp ≠ 0 :=
    ne_of_gt (by positivity)
  have ht := (S.tendsto_phaseDensity_over_square hκ hχ (ne_of_gt hc)).div
    (S.tendsto_compactness_over_square (ne_of_gt hG) (ne_of_gt hc)) hn
  have he : (fun r => phaseDensity κ χ mf G c hp S.potential r / compactnessRatio G c r (S.mass r))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun r => (phaseDensity κ χ mf G c hp S.potential r / r ^ 2) /
        (compactnessRatio G c r (S.mass r) / r ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hnr : r ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (show 0 < r from hr))
    simp only [div_div_div_cancel_right₀ hnr]
  apply (tendsto_congr' he).mpr
  convert ht using 1 <;> try rfl
  field_simp


end CenterSeed

end AppendixB

/-! ## 9. Remaining scope

The kinetic differentiation gap is now closed for A and B (the moments
needed for density and pressure derivatives). The moving cutoff, vanishing
endpoint term, domination under the pulled-back integral, and integrability
of the inverse-square-root C kernel have all been proved. The exact kinetic
moments satisfy positivity and Cauchy--Schwarz, and therefore construct the
abstract Moments used in the earlier barrier proofs.

Key EOS theorems in AppendixB:
* hasDerivAt_momentA: A_u = β(4A+3B).
* hasDerivAt_momentB: B_u = β(2B+C).
* hasDerivAt_densityEnergy: ρ_u = Ckin β(4A+5B+C).
* hasDerivAt_pressureMass: Π_u = Ckin β(4A/3+B), with Π=P/c².
* EOS_derivative_ratio and EOS_slope_envelope: the actual derivative ratio
  agrees with Moments.a and satisfies the global envelope.
* kinetic_EOS_field_domination: the actual EOS supplies the comparator.
* pressureMass_derivative_enthalpy: Π_u = β(ρ+Π).

The endpoint asymptotic gap is also closed for this energy-integral model:
* densityEnergy_low_asymptotic and pressureEnergy_low_asymptotic give the
  exact coefficients ρ₀ and P₀ and their u^(5/2), u^(7/2) powers.
* polytropic_low_asymptotic proves P ~ P₀(ρ/ρ₀)^(7/5) along the EOS.
* tendsto_EOS_w_over_u and tendsto_EOS_derivative_ratio_over_u prove the
  low-density coefficients of the actual ratios, not just abstract moments.
* tendsto_kineticSlope_div_W_low proves a/w -> 7/5.
* densityEnergy_relativistic_asymptotic and
  pressureEnergy_relativistic_asymptotic give the exact δ^(-4) coefficients.
* momentC_high_isBigO_log proves C = O(log(1/δ)).
* tendsto_densityEnergy_atTop, radiation_relativistic_asymptotic, and
  tendsto_EOS_derivative_ratio_relativistic give density divergence,
  P ~ (c²/3)ρ, and a -> 1/3. w -> 1/3 is also proved.

The local regular-center existence gap is now closed:
* exists_physical_regular_TOV constructs m,u on a nonzero interval [0,R].
* The actual mass and pressure equations, u(0)=uc, m(0)=0, and u'(0)=0
  are proved, with u remaining in its physical kinetic domain and x≤1/2.
* Density is strictly decreasing, mass is positive for r>0, and
  CenterSeed.phase_wedge proves 0<y<3x.
* CenterSeed.tendsto_mass_over_cube proves m/r³ -> 4πρc/3.
* CenterSeed.tendsto_compactness_over_square and
  CenterSeed.tendsto_phaseDensity_over_square prove the quadratic center
  coefficients; tendsto_phaseDensity_div_compactness proves y/x -> 3.
* exists_tov_interior_physical supplies local existence at every physical
  positive-radius state. These results use the actual kinetic EOS.

Still outside this file:
1. Pressure normalization/change of variable connecting the slide integrals
   to the energy integrals.
2. Global maximal continuation, a finite vacuum surface, and uniqueness of
   all regular-center solutions. Also, the log-radius phase ODE conversion
   and its application to the maximal branch using
   moments_path_diagonal_compactness. Local center existence, the strict
   wedge, and the center expansions have been proved above.
3. The simpler Lambert/barrier root. The sharper diagonal root is now
   proved unique, enclosed in (0.6734385928, 0.6734385929), and connected
   to the original potentials by the appended numerical-root section.

These remaining inputs are not concealed behind custom axioms. The file has
no sorry placeholders and no new axiom declarations. Local physical TOV
existence is formally verified; this file does not claim that the complete
global boundary-value problem or all manuscript results have been verified.
-/

end RARTOV


/-!
# Certified sharper RAR/TOV scalar root

Validation target: Lean 4.19.0, Mathlib v4.19.0.
Run in a Mathlib project: lake env lean RAR-TOV-with-Appendix-B.lean

The root is defined by UStar x + JStar x = EStar on (zStar, 1).
The logarithm certificates use Mathlib's proved Taylor remainder inequality.
All decimal bounds are exact rational numbers. Floating point computations
are used only to choose candidate bounds; Lean proves every bound anew.
-/

noncomputable section
open Set
open scoped BigOperators
namespace RARTOVNumericalRoot

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def zStar : ℝ := (18 - 4 * Real.sqrt 3) / 23
def xiStar : ℝ := (8 - 2 * Real.sqrt 3) / 13
def YStar : ℝ := 3 * xiStar
def hStar : ℝ := (5 + Real.sqrt 3) / 2
def bStar : ℝ := hStar * (1 - zStar)
def UStar (x : ℝ) : ℝ :=
  hStar * (zStar - x) + bStar * Real.log ((1 - zStar) / (1 - x))
def JStar (x : ℝ) : ℝ := x - zStar - zStar * Real.log (x / zStar)
def EStar : ℝ := YStar - zStar - zStar * Real.log (YStar / zStar)
def rootEq (x : ℝ) : ℝ := UStar x + JStar x - EStar

def lower : ℝ := 6734385928 / 10^10
def upper : ℝ := 6734385929 / 10^10

/-- Rational Taylor polynomial for -log(1-t). -/
def logPoly (t : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, t ^ (i + 1) / (i + 1)

/-- A certificate rule: logarithm bounds follow from finite rational checks. -/
theorem log_rational_bounds (q L H : ℝ) (n : ℕ)
    (hq : 1 ≤ q)
    (hL : L ≤ logPoly (1 - q⁻¹) n - (1 - q⁻¹)^(n+1) / (1 - (1 - q⁻¹)))
    (hH : logPoly (1 - q⁻¹) n + (1 - q⁻¹)^(n+1) / (1 - (1 - q⁻¹)) ≤ H) :
    L ≤ Real.log q ∧ Real.log q ≤ H := by
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have ht0 : 0 ≤ 1-q⁻¹ := sub_nonneg.mpr ((inv_le_one₀ hqp).mpr hq)
  have ht : |1-q⁻¹| < 1 := by
    rw [abs_of_nonneg ht0]
    linarith [inv_pos.mpr hqp]
  have hr := Real.abs_log_sub_add_sum_range_le ht n
  have he : 1 - (1 - q⁻¹) = q⁻¹ := by ring
  rw [he, Real.log_inv, abs_of_nonneg ht0] at hr
  change |logPoly (1 - q⁻¹) n - Real.log q| ≤ _ at hr
  have hh := abs_le.mp hr
  constructor <;> linarith

private theorem positive_mul_bounds {a a₀ a₁ b b₀ b₁ : ℝ}
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀)
    (ha : a₀ ≤ a ∧ a ≤ a₁) (hb : b₀ ≤ b ∧ b ≤ b₁) :
    a₀*b₀ ≤ a*b ∧ a*b ≤ a₁*b₁ := by
  have hap : 0 ≤ a := ha₀.trans ha.1
  have hbp : 0 ≤ b := hb₀.trans hb.1
  constructor
  · exact mul_le_mul ha.1 hb.1 hb₀ hap
  · exact mul_le_mul ha.2 hb.2 hbp (hap.trans ha.2)

private theorem sqrt_three_bounds :
    (1732050807568877293 : ℝ)/10^18 ≤ Real.sqrt 3 ∧
    Real.sqrt 3 ≤ (1732050807568877294 : ℝ)/10^18 := by
  have hp := Real.sqrt_nonneg (3 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  constructor <;> nlinarith

private theorem zStar_bounds :
    (481382468248890904 : ℝ)/1000000000000000000 ≤ zStar ∧
    zStar ≤ (481382468248890907 : ℝ)/1000000000000000000 := by
  have hs := sqrt_three_bounds
  unfold zStar
  constructor <;> linarith

private theorem hStar_bounds :
    (3366025403784438645 : ℝ)/1000000000000000000 ≤ hStar ∧
    hStar ≤ (3366025403784438648 : ℝ)/1000000000000000000 := by
  have hs := sqrt_three_bounds
  unfold hStar
  constructor <;> linarith

private theorem YStar_bounds :
    (1046745781122056632 : ℝ)/1000000000000000000 ≤ YStar ∧
    YStar ≤ (1046745781122056635 : ℝ)/1000000000000000000 := by
  have hs := sqrt_three_bounds
  unfold YStar xiStar
  constructor <;> linarith

private theorem bStar_bounds :
    (17456797867222158 : ℝ)/10000000000000000 ≤ bStar ∧
    bStar ≤ (17456797867222161 : ℝ)/10000000000000000 := by
  have hm := positive_mul_bounds
    (show (0 : ℝ) ≤ 3366025403784438645/1000000000000000000 by norm_num)
    (show (0 : ℝ) ≤ 1 - 481382468248890907/1000000000000000000 by norm_num)
    hStar_bounds
    (show 1 - (481382468248890907 : ℝ)/1000000000000000000 ≤ 1-zStar ∧
      1-zStar ≤ 1 - (481382468248890904 : ℝ)/1000000000000000000 by
        have hz := zStar_bounds; constructor <;> linarith)
  unfold bStar
  constructor <;> linarith [hm.1, hm.2]

theorem zStar_pos : 0 < zStar := by
  have hz := zStar_bounds; linarith

theorem zStar_lt_lower : zStar < lower := by
  have hz := zStar_bounds; norm_num [lower] at *; linarith

theorem lower_lt_upper : lower < upper := by norm_num [lower, upper]
theorem upper_lt_one : upper < 1 := by norm_num [upper]

/-- The two-log residual used by the numerical calculation equals rootEq. -/
theorem rootEq_two_logs {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    rootEq x =
      -(hStar-1)*(x-zStar) +
        bStar * Real.log ((1-zStar)/(1-x)) +
        zStar-YStar + zStar * Real.log (YStar/x) := by
  have hz := zStar_pos
  have hy : 0 < YStar := by have hh := YStar_bounds; linarith
  unfold rootEq UStar JStar EStar
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hz),
      Real.log_div (ne_of_gt hy) (ne_of_gt hz),
      Real.log_div (ne_of_gt hy) (ne_of_gt hx)]
  ring

private theorem log_lower_A_lo :
    (46254867024063 : ℝ)/10^14 ≤ Real.log ((15881164164431890 : ℝ)/10^16) ∧
    Real.log ((15881164164431890 : ℝ)/10^16) ≤ (46254867024068 : ℝ)/10^14 := by
  apply log_rational_bounds _ _ _ 40
  · norm_num
  · norm_num [logPoly, Finset.sum_range_succ]
  · norm_num [logPoly, Finset.sum_range_succ]

private theorem log_lower_A_hi :
    (46254867024063 : ℝ)/10^14 ≤ Real.log ((15881164164431895 : ℝ)/10^16) ∧
    Real.log ((15881164164431895 : ℝ)/10^16) ≤ (46254867024068 : ℝ)/10^14 := by
  apply log_rational_bounds _ _ _ 40
  · norm_num
  · norm_num [logPoly, Finset.sum_range_succ]
  · norm_num [logPoly, Finset.sum_range_succ]

private theorem arg_lower_A_bounds :
    (15881164164431890 : ℝ)/10^16 ≤ (1-zStar)/(1-lower) ∧
    (1-zStar)/(1-lower) ≤ (15881164164431895 : ℝ)/10^16 := by
  have hb := zStar_bounds
  have hd : 0 < 1-lower := by norm_num [lower]
  constructor
  · apply (le_div_iff₀ hd).mpr
    norm_num [lower]
    linarith
  · apply (div_le_iff₀ hd).mpr
    norm_num [lower]
    linarith

private theorem log_lower_A_bounds :
    (46254867024063 : ℝ)/10^14 ≤ Real.log ((1-zStar)/(1-lower)) ∧
    Real.log ((1-zStar)/(1-lower)) ≤ (46254867024068 : ℝ)/10^14 := by
  have hb := arg_lower_A_bounds
  constructor
  · exact log_lower_A_lo.1.trans
      (Real.log_le_log (by norm_num) hb.1)
  · have hp : 0 < (1-zStar)/(1-lower) := lt_of_lt_of_le (by norm_num) hb.1
    exact (Real.log_le_log hp hb.2).trans log_lower_A_hi.2

private theorem log_lower_B_lo :
    (44104455898679 : ℝ)/10^14 ≤ Real.log ((15543299601674632 : ℝ)/10^16) ∧
    Real.log ((15543299601674632 : ℝ)/10^16) ≤ (44104455898684 : ℝ)/10^14 := by
  apply log_rational_bounds _ _ _ 40
  · norm_num
  · norm_num [logPoly, Finset.sum_range_succ]
  · norm_num [logPoly, Finset.sum_range_succ]

private theorem log_lower_B_hi :
    (44104455898679 : ℝ)/10^14 ≤ Real.log ((15543299601674637 : ℝ)/10^16) ∧
    Real.log ((15543299601674637 : ℝ)/10^16) ≤ (44104455898684 : ℝ)/10^14 := by
  apply log_rational_bounds _ _ _ 40
  · norm_num
  · norm_num [logPoly, Finset.sum_range_succ]
  · norm_num [logPoly, Finset.sum_range_succ]

private theorem arg_lower_B_bounds :
    (15543299601674632 : ℝ)/10^16 ≤ YStar/lower ∧
    YStar/lower ≤ (15543299601674637 : ℝ)/10^16 := by
  have hb := YStar_bounds
  have hd : 0 < lower := by norm_num [lower]
  constructor
  · apply (le_div_iff₀ hd).mpr
    norm_num [lower]
    linarith
  · apply (div_le_iff₀ hd).mpr
    norm_num [lower]
    linarith

private theorem log_lower_B_bounds :
    (44104455898679 : ℝ)/10^14 ≤ Real.log (YStar/lower) ∧
    Real.log (YStar/lower) ≤ (44104455898684 : ℝ)/10^14 := by
  have hb := arg_lower_B_bounds
  constructor
  · exact log_lower_B_lo.1.trans
      (Real.log_le_log (by norm_num) hb.1)
  · have hp : 0 < YStar/lower := lt_of_lt_of_le (by norm_num) hb.1
    exact (Real.log_le_log hp hb.2).trans log_lower_B_hi.2

theorem rootEq_lower_neg : rootEq lower < 0 := by
  have hx : 0 < lower := by norm_num [lower]
  rw [rootEq_two_logs hx (by norm_num [lower])]
  have hp := positive_mul_bounds
    (show (0 : ℝ) ≤ 3366025403784438645/1000000000000000000-1 by norm_num)
    (show (0 : ℝ) ≤ lower-481382468248890907/1000000000000000000 by norm_num [lower])
    (show (3366025403784438645 : ℝ)/1000000000000000000-1 ≤ hStar-1 ∧
      hStar-1 ≤ (3366025403784438648 : ℝ)/1000000000000000000-1 by
        have hh := hStar_bounds; constructor <;> linarith)
    (show lower-(481382468248890907 : ℝ)/1000000000000000000 ≤ lower-zStar ∧
      lower-zStar ≤ lower-(481382468248890904 : ℝ)/1000000000000000000 by
        have hh := zStar_bounds; constructor <;> linarith)
  have hA := positive_mul_bounds
    (show (0 : ℝ) ≤ 17456797867222158/10000000000000000 by norm_num)
    (show (0 : ℝ) ≤ 46254867024063/10^14 by norm_num)
    bStar_bounds log_lower_A_bounds
  have hB := positive_mul_bounds
    (show (0 : ℝ) ≤ 481382468248890904/1000000000000000000 by norm_num)
    (show (0 : ℝ) ≤ 44104455898679/10^14 by norm_num)
    zStar_bounds log_lower_B_bounds
  have hz := zStar_bounds
  have hy := YStar_bounds
  norm_num [lower] at hp hA hB ⊢
  nlinarith only [hp.1, hp.2, hA.1, hA.2, hB.1, hB.2, hz.1, hz.2, hy.1, hy.2]

private theorem log_upper_A_lo :
    (46254867054685 : ℝ)/10^14 ≤ Real.log ((15881164169295038 : ℝ)/10^16) ∧
    Real.log ((15881164169295038 : ℝ)/10^16) ≤ (46254867054690 : ℝ)/10^14 := by
  apply log_rational_bounds _ _ _ 40
  · norm_num
  · norm_num [logPoly, Finset.sum_range_succ]
  · norm_num [logPoly, Finset.sum_range_succ]

private theorem log_upper_A_hi :
    (46254867054685 : ℝ)/10^14 ≤ Real.log ((15881164169295043 : ℝ)/10^16) ∧
    Real.log ((15881164169295043 : ℝ)/10^16) ≤ (46254867054690 : ℝ)/10^14 := by
  apply log_rational_bounds _ _ _ 40
  · norm_num
  · norm_num [logPoly, Finset.sum_range_succ]
  · norm_num [logPoly, Finset.sum_range_succ]

private theorem arg_upper_A_bounds :
    (15881164169295038 : ℝ)/10^16 ≤ (1-zStar)/(1-upper) ∧
    (1-zStar)/(1-upper) ≤ (15881164169295043 : ℝ)/10^16 := by
  have hb := zStar_bounds
  have hd : 0 < 1-upper := by norm_num [upper]
  constructor
  · apply (le_div_iff₀ hd).mpr
    norm_num [upper]
    linarith
  · apply (div_le_iff₀ hd).mpr
    norm_num [upper]
    linarith

private theorem log_upper_A_bounds :
    (46254867054685 : ℝ)/10^14 ≤ Real.log ((1-zStar)/(1-upper)) ∧
    Real.log ((1-zStar)/(1-upper)) ≤ (46254867054690 : ℝ)/10^14 := by
  have hb := arg_upper_A_bounds
  constructor
  · exact log_upper_A_lo.1.trans
      (Real.log_le_log (by norm_num) hb.1)
  · have hp : 0 < (1-zStar)/(1-upper) := lt_of_lt_of_le (by norm_num) hb.1
    exact (Real.log_le_log hp hb.2).trans log_upper_A_hi.2

private theorem log_upper_B_lo :
    (44104455883830 : ℝ)/10^14 ≤ Real.log ((15543299599366582 : ℝ)/10^16) ∧
    Real.log ((15543299599366582 : ℝ)/10^16) ≤ (44104455883835 : ℝ)/10^14 := by
  apply log_rational_bounds _ _ _ 40
  · norm_num
  · norm_num [logPoly, Finset.sum_range_succ]
  · norm_num [logPoly, Finset.sum_range_succ]

private theorem log_upper_B_hi :
    (44104455883830 : ℝ)/10^14 ≤ Real.log ((15543299599366587 : ℝ)/10^16) ∧
    Real.log ((15543299599366587 : ℝ)/10^16) ≤ (44104455883835 : ℝ)/10^14 := by
  apply log_rational_bounds _ _ _ 40
  · norm_num
  · norm_num [logPoly, Finset.sum_range_succ]
  · norm_num [logPoly, Finset.sum_range_succ]

private theorem arg_upper_B_bounds :
    (15543299599366582 : ℝ)/10^16 ≤ YStar/upper ∧
    YStar/upper ≤ (15543299599366587 : ℝ)/10^16 := by
  have hb := YStar_bounds
  have hd : 0 < upper := by norm_num [upper]
  constructor
  · apply (le_div_iff₀ hd).mpr
    norm_num [upper]
    linarith
  · apply (div_le_iff₀ hd).mpr
    norm_num [upper]
    linarith

private theorem log_upper_B_bounds :
    (44104455883830 : ℝ)/10^14 ≤ Real.log (YStar/upper) ∧
    Real.log (YStar/upper) ≤ (44104455883835 : ℝ)/10^14 := by
  have hb := arg_upper_B_bounds
  constructor
  · exact log_upper_B_lo.1.trans
      (Real.log_le_log (by norm_num) hb.1)
  · have hp : 0 < YStar/upper := lt_of_lt_of_le (by norm_num) hb.1
    exact (Real.log_le_log hp hb.2).trans log_upper_B_hi.2

theorem rootEq_upper_pos : 0 < rootEq upper := by
  have hx : 0 < upper := by norm_num [upper]
  rw [rootEq_two_logs hx (by norm_num [upper])]
  have hp := positive_mul_bounds
    (show (0 : ℝ) ≤ 3366025403784438645/1000000000000000000-1 by norm_num)
    (show (0 : ℝ) ≤ upper-481382468248890907/1000000000000000000 by norm_num [upper])
    (show (3366025403784438645 : ℝ)/1000000000000000000-1 ≤ hStar-1 ∧
      hStar-1 ≤ (3366025403784438648 : ℝ)/1000000000000000000-1 by
        have hh := hStar_bounds; constructor <;> linarith)
    (show upper-(481382468248890907 : ℝ)/1000000000000000000 ≤ upper-zStar ∧
      upper-zStar ≤ upper-(481382468248890904 : ℝ)/1000000000000000000 by
        have hh := zStar_bounds; constructor <;> linarith)
  have hA := positive_mul_bounds
    (show (0 : ℝ) ≤ 17456797867222158/10000000000000000 by norm_num)
    (show (0 : ℝ) ≤ 46254867054685/10^14 by norm_num)
    bStar_bounds log_upper_A_bounds
  have hB := positive_mul_bounds
    (show (0 : ℝ) ≤ 481382468248890904/1000000000000000000 by norm_num)
    (show (0 : ℝ) ≤ 44104455883830/10^14 by norm_num)
    zStar_bounds log_upper_B_bounds
  have hz := zStar_bounds
  have hy := YStar_bounds
  norm_num [upper] at hp hA hB ⊢
  nlinarith only [hp.1, hp.2, hA.1, hA.2, hB.1, hB.2, hz.1, hz.2, hy.1, hy.2]

/-! ## Analytic root theorem -/

/-- A log-difference presentation makes differentiation transparent. -/
private theorem rootEq_log_form {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    rootEq x = hStar*(zStar-x) +
      bStar*(Real.log (1-zStar)-Real.log (1-x)) +
      x-zStar-zStar*(Real.log x-Real.log zStar)-EStar := by
  have hz1 : zStar < 1 := lt_trans zStar_lt_lower
    (lt_trans lower_lt_upper upper_lt_one)
  unfold rootEq UStar JStar
  rw [Real.log_div (ne_of_gt (sub_pos.mpr hz1))
      (ne_of_gt (sub_pos.mpr hx1)),
      Real.log_div (ne_of_gt hx) (ne_of_gt zStar_pos)]
  ring

private def logResidual (x : ℝ) : ℝ :=
  hStar*(zStar-x) + bStar*(Real.log (1-zStar)-Real.log (1-x)) +
    x-zStar-zStar*(Real.log x-Real.log zStar)-EStar

private theorem hasDerivAt_logResidual {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt logResidual
      (hStar*(x-zStar)/(1-x) + (1-zStar/x)) x := by
  have hn : 1-x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hlin : HasDerivAt (fun t : ℝ => zStar-t) (-1) x := by
    convert (hasDerivAt_const x zStar).sub (hasDerivAt_id x) using 1 <;> first | rfl | ring
  have hlog : HasDerivAt (fun t : ℝ => Real.log (1-t)) (-1/(1-x)) x := by
    simpa using ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log hn
  have hlx := (Real.hasDerivAt_log (ne_of_gt hx)).sub_const (Real.log zStar)
  have hd := (((((hlin.const_mul hStar).add
      (((hasDerivAt_const x (Real.log (1-zStar))).sub hlog).const_mul bStar)).add
      (hasDerivAt_id x)).sub_const zStar).sub (hlx.const_mul zStar)).sub_const EStar
  convert hd using 1 <;> try rfl
  unfold bStar
  field_simp [hn, ne_of_gt hx]
  ring

theorem rootEq_strictMonoOn : StrictMonoOn rootEq (Ioo zStar 1) := by
  have hlog : StrictMonoOn logResidual (Ioo zStar 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo zStar 1)
    · intro x hx
      exact (hasDerivAt_logResidual (lt_trans zStar_pos hx.1) hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      have xp : 0 < x := lt_trans zStar_pos hx.1
      rw [(hasDerivAt_logResidual xp hx.2).deriv]
      have hp : 0 < hStar := by have hh := hStar_bounds; linarith
      have hterm : 0 < hStar*(x-zStar)/(1-x) :=
        div_pos (mul_pos hp (sub_pos.mpr hx.1)) (sub_pos.mpr hx.2)
      have hratio : zStar/x < 1 := (div_lt_one xp).mpr hx.1
      linarith
  intro x hx y hy hxy
  rw [rootEq_log_form (lt_trans zStar_pos hx.1) hx.2,
      rootEq_log_form (lt_trans zStar_pos hy.1) hy.2]
  exact hlog hx hy hxy

theorem rootEq_continuousOn : ContinuousOn rootEq (Icc lower upper) := by
  intro x hx
  have xp : 0 < x := lt_trans zStar_pos (lt_of_lt_of_le zStar_lt_lower hx.1)
  have x1 : x < 1 := lt_of_le_of_lt hx.2 upper_lt_one
  have hres : ContinuousWithinAt logResidual (Icc lower upper) x :=
    (hasDerivAt_logResidual xp x1).continuousAt.continuousWithinAt
  apply hres.congr_of_mem _ hx
  intro t ht
  exact rootEq_log_form
    (lt_trans zStar_pos (lt_of_lt_of_le zStar_lt_lower ht.1))
    (lt_of_le_of_lt ht.2 upper_lt_one)

/-- Existence in the strict certified interval, not assumed in the definition. -/
theorem exists_root_in_bracket : ∃ x : ℝ, lower < x ∧ x < upper ∧ rootEq x = 0 := by
  have hivt := intermediate_value_Icc lower_lt_upper.le rootEq_continuousOn
    (show (0 : ℝ) ∈ Icc (rootEq lower) (rootEq upper) from
      ⟨rootEq_lower_neg.le, rootEq_upper_pos.le⟩)
  obtain ⟨x, hx, he⟩ := hivt
  have hxl : lower < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro hh
    subst x
    linarith [rootEq_lower_neg]
  have hxu : x < upper := by
    refine lt_of_le_of_ne hx.2 ?_
    intro hh
    subst x
    linarith [rootEq_upper_pos]
  exact ⟨x, hxl, hxu, he⟩

/-- There is exactly one zero on the full physical domain (zStar,1). -/
theorem existsUnique_root : ∃! x : ℝ, x ∈ Ioo zStar 1 ∧ rootEq x = 0 := by
  obtain ⟨x, hxl, hxu, he⟩ := exists_root_in_bracket
  have hx : x ∈ Ioo zStar 1 :=
    ⟨lt_trans zStar_lt_lower hxl, lt_trans hxu upper_lt_one⟩
  refine ⟨x, ⟨hx, he⟩, ?_⟩
  intro y hy
  exact rootEq_strictMonoOn.injOn hy.1 hx (hy.2.trans he.symm)

/-- The exact root, chosen only after proving existence. -/
def Xsharp : ℝ := Classical.choose exists_root_in_bracket

theorem Xsharp_bracket :
    (6734385928 : ℝ)/10^10 < Xsharp ∧
    Xsharp < (6734385929 : ℝ)/10^10 := by
  exact ⟨(Classical.choose_spec exists_root_in_bracket).1,
    (Classical.choose_spec exists_root_in_bracket).2.1⟩

theorem Xsharp_root : UStar Xsharp + JStar Xsharp = EStar := by
  have he := (Classical.choose_spec exists_root_in_bracket).2.2
  change UStar Xsharp + JStar Xsharp - EStar = 0 at he
  linarith

theorem Xsharp_domain : zStar < Xsharp ∧ Xsharp < 1 := by
  exact ⟨lt_trans zStar_lt_lower Xsharp_bracket.1,
    lt_trans Xsharp_bracket.2 upper_lt_one⟩

theorem root_eq_Xsharp {x : ℝ} (hx : zStar < x) (hx1 : x < 1)
    (he : UStar x + JStar x = EStar) : x = Xsharp := by
  apply rootEq_strictMonoOn.injOn ⟨hx,hx1⟩ Xsharp_domain
  have hzero : rootEq x = 0 := by unfold rootEq; linarith
  exact hzero.trans (Classical.choose_spec exists_root_in_bracket).2.2.symm

end RARTOVNumericalRoot

#print axioms RARTOVNumericalRoot.log_rational_bounds
#print axioms RARTOVNumericalRoot.rootEq_lower_neg
#print axioms RARTOVNumericalRoot.rootEq_upper_pos
#print axioms RARTOVNumericalRoot.existsUnique_root
#print axioms RARTOVNumericalRoot.Xsharp_bracket
#print axioms RARTOVNumericalRoot.Xsharp_root

/-! ## Certified root applied to the original RARTOV potentials -/
namespace RARTOV

open RARTOVNumericalRoot

theorem z_kStar_eq_zStar : z kStar = zStar := by
  have hs : (Real.sqrt (3 : ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hc : (Real.sqrt (3 : ℝ))^3 = 3*Real.sqrt 3 := by
    calc
      (Real.sqrt (3 : ℝ))^3 = (Real.sqrt 3)^2 * Real.sqrt 3 := by ring
      _ = 3*Real.sqrt 3 := by rw [hs]
  unfold z kStar zStar
  field_simp [hn]
  nlinarith [hs, hc]

theorem xi_kStar_eq_xiStar : xi kStar = xiStar := by
  have hs : (Real.sqrt (3 : ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hc : (Real.sqrt (3 : ℝ)) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      (Real.sqrt (3 : ℝ)) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hs]
  unfold xi kStar xiStar
  field_simp [hn]
  nlinarith [hs, hc]

theorem h_kStar_eq_hStar : h kStar = hStar := by
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  unfold h kStar hStar
  field_simp [hn]
  ring

theorem cap_kStar_eq_YStar : cap kStar = YStar := by
  simp [cap, YStar, xi_kStar_eq_xiStar]

theorem b_kStar_eq_bStar : b kStar = bStar := by
  simp [b, bStar, h_kStar_eq_hStar, z_kStar_eq_zStar]

theorem U_kStar_eq_UStar {x : ℝ} (hx1 : x < 1) : U kStar x = UStar x := by
  have hz1 : zStar < 1 := by rw [← z_kStar_eq_zStar]; exact z_lt_one kStar kStar_pos
  unfold U UStar
  rw [z_kStar_eq_zStar, h_kStar_eq_hStar, b_kStar_eq_bStar,
      Real.log_div (ne_of_gt (sub_pos.mpr hz1)) (ne_of_gt (sub_pos.mpr hx1))]

theorem J_kStar_eq_JStar {x : ℝ} (hx : 0 < x) : J kStar x = JStar x := by
  unfold J JStar
  rw [z_kStar_eq_zStar, Real.log_div (ne_of_gt hx) (ne_of_gt zStar_pos)]

theorem level_kStar_eq_EStar : level kStar = EStar := by
  have hp : 0 < YStar := by rw [← cap_kStar_eq_YStar]; exact lt_trans (z_pos kStar kStar_pos) (z_lt_cap kStar kStar_pos)
  rw [level, cap_kStar_eq_YStar, J_kStar_eq_JStar hp]
  rfl

/-- The exact sharper root for the original barrier theorems. -/
abbrev Xsharp : ℝ := RARTOVNumericalRoot.Xsharp

theorem Xsharp_bracket :
    (6734385928 : ℝ)/10^10 < Xsharp ∧ Xsharp < (6734385929 : ℝ)/10^10 :=
  RARTOVNumericalRoot.Xsharp_bracket

theorem Xsharp_domain : z kStar < Xsharp ∧ Xsharp < 1 := by
  rw [z_kStar_eq_zStar]
  exact RARTOVNumericalRoot.Xsharp_domain

theorem Xsharp_root : U kStar Xsharp + J kStar Xsharp = level kStar := by
  rw [U_kStar_eq_UStar Xsharp_domain.2,
      J_kStar_eq_JStar (lt_trans (z_pos kStar kStar_pos) Xsharp_domain.1),
      level_kStar_eq_EStar]
  exact RARTOVNumericalRoot.Xsharp_root

theorem sharper_root_unique {X : ℝ} (hXz : z kStar < X) (hX1 : X < 1)
    (hroot : U kStar X + J kStar X = level kStar) : X = Xsharp := by
  apply RARTOVNumericalRoot.root_eq_Xsharp
  · rwa [z_kStar_eq_zStar] at hXz
  · exact hX1
  · rwa [U_kStar_eq_UStar hX1,
      J_kStar_eq_JStar (lt_trans (z_pos kStar kStar_pos) hXz),
      level_kStar_eq_EStar] at hroot

/-- The original path theorem instantiated with the certified exact root.
The scalar-root hypotheses are proved; the physical path hypotheses remain explicit. -/
theorem moments_path_diagonal_compactness_certified (s0 s1 : ℝ)
    (m : ℝ → Moments) (x y : ℝ → ℝ)
    (hxpos : ∀ t ∈ Icc s0 s1, 0 < x t)
    (hx1 : ∀ t ∈ Icc s0 s1, x t < 1)
    (hypos : ∀ t ∈ Icc s0 s1, 0 < y t)
    (hwed : ∀ t ∈ Icc s0 s1, y t < 3*x t)
    (hxderiv : ∀ t ∈ Icc s0 s1, HasDerivAt x (y t-x t) t)
    (hyderiv : ∀ t ∈ Icc s0 s1,
      HasDerivAt y (nonlinearField (m t).w (m t).a (x t) (y t)) t)
    (hstartX : x s0 ≤ z kStar) (hstartY : y s0 ≤ z kStar) :
    ∀ t ∈ Icc s0 s1, x t ≤ Xsharp ∧ x t < (6734385929 : ℝ)/10^10 := by
  have hb := moments_path_diagonal_compactness Xsharp s0 s1 m x y
    Xsharp_domain.1 Xsharp_domain.2 Xsharp_root
    hxpos hx1 hypos hwed hxderiv hyderiv hstartX hstartY
  intro t ht
  exact ⟨hb t ht, lt_of_le_of_lt (hb t ht) Xsharp_bracket.2⟩

end RARTOV

#print axioms RARTOV.AppendixB.exists_physical_regular_TOV
#print axioms RARTOV.AppendixB.polytropic_low_asymptotic
#print axioms RARTOV.AppendixB.radiation_relativistic_asymptotic
#print axioms RARTOV.Xsharp_root
#print axioms RARTOV.Xsharp_bracket
#print axioms RARTOV.moments_path_diagonal_compactness_certified
