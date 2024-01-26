/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Probability.Notation
import Mathlib.Data.Real.NNReal
import Mathlib.Probability.Density
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Probability.Variance
/-!
# Characteristic function of a measure

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



-/


open MeasureTheory ComplexConjugate Complex

open scoped RealInnerProductSpace

section character

open scoped FourierTransform Real

/-- The additive character of `ℝ` given by `fun x ↦ exp (- x * I)`. -/
noncomputable
def probFourierChar : Multiplicative ℝ →* circle where
  toFun z := expMapCircle (- Multiplicative.toAdd z)
  map_one' := by simp only;rw [toAdd_one, neg_zero, expMapCircle_zero]
  map_mul' x y := by simp only; rw [toAdd_mul, neg_add, expMapCircle_add]

theorem probFourierChar_apply' (x : ℝ) : probFourierChar[x] = exp (↑(-x) * I) := rfl

theorem probFourierChar_apply (x : ℝ) : probFourierChar[x] = exp (- ↑x * I) := by
  simp only [probFourierChar_apply', ofReal_neg]
--定义好了基本的傅里叶变换

@[continuity]
theorem continuous_probFourierChar : Continuous probFourierChar :=
  (map_continuous expMapCircle).comp continuous_toAdd.neg
--连续性的延拓

variable {E : Type _} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℂ E]

theorem fourierIntegral_probFourierChar_eq_integral_exp {V : Type _} [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace V] {W : Type _} [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (μ : Measure V) (f : V → E) (w : W) :
    VectorFourier.fourierIntegral probFourierChar μ L f w =
      ∫ v : V, exp (↑(L v w) * I) • f v ∂μ := by
    simp_rw[VectorFourier.fourierIntegral,probFourierChar_apply,ofReal_neg,neg_neg]
--定义好了傅里叶的积分

end character

open scoped Real
open MeasureTheory
open Set BigOperators NNReal

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]
variable {Ω : Type*} [MeasurableSpace Ω] (_ℙ : Measure Ω) [MeasureSpace Ω]

/-- The characteristic function of a measure. -/
noncomputable
def charFun [Inner ℝ E] (μ : Measure E) (t : E) : ℂ := ∫ x, exp (⟪t, x⟫ • I) ∂μ

noncomputable
def charFun_of [Inner ℝ E] (X : Ω → E) (_ℙ : Measure Ω) (t : E) : ℂ := ∫ (x : Ω), exp (⟪t, X x⟫ • I) ∂_ℙ

/- 和随机变量相关联的特征函数 -/
lemma charFun_ofvariable [Inner ℝ E] (μ : Measure E) (_ℙ : Measure Ω) (t : E) (X : Ω → E) (h : HasPDF X _ℙ μ) :
    ∫ (x : Ω), exp (⟪t, X x⟫ • I) ∂_ℙ = ∫ (x : E), exp (⟪t, x⟫ • I) ∂μ := by
  sorry

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma charFun_eq_fourierIntegral (μ : Measure E) (t : E) :
    charFun μ t = VectorFourier.fourierIntegral probFourierChar μ sesqFormOfInner
      (fun _ ↦ (1 : ℂ)) t := by
  simp only [charFun, fourierIntegral_probFourierChar_eq_integral_exp, real_smul, smul_eq_mul,
    mul_one]
  congr
--定义好了特征函数定义与前面相符合


/- 高斯分布的定义 -/
-- notice that we define the range to be in ℝ≥0, which can be converted to ENNReal when in use
noncomputable
def gaussianPdf (μ : ℝ)(v : ℝ≥0 ) (x : ℝ) : ℝ≥0 :=
  ⟨(Real.sqrt (2 * π  * v))⁻¹ * Real.exp (- (x - μ)^2 / (2 * v)), by positivity⟩

noncomputable
def Gaussian_Distribution (μ : ℝ) (v : ℝ≥0 ) : Measure ℝ := volume.withDensity (gaussianPdf μ v ·)

def real_to_nnreal (x : ENNReal) : ℝ≥0 := ENNReal.toNNReal x

noncomputable
def gaussianPdf_nnreal (μ : ℝ)(v : ℝ≥0 ) (x : ℝ) : ℝ≥0 := real_to_nnreal (gaussianPdf μ v x)

-- one 'sorry' needed to be clear,
lemma gaussian_integral_var_change (μ : ℝ) (v : ℝ≥0 )(t : ℝ )(f : ℝ  → ℂ ) :
    ∫ (x : ℝ), f x ∂Gaussian_Distribution μ v = ∫ (x : ℝ), (f x) * (gaussianPdf μ v x) := by
  dsimp [Gaussian_Distribution]
  have h : gaussianPdf μ v = fun x => gaussianPdf μ v x := rfl
  simp [h]
  have g_meas : Measurable fun x => gaussianPdf μ v x:= by sorry
  rw [integral_withDensity_eq_integral_smul g_meas]
  congr
  ext x
  dsimp
  rw [NNReal.smul_def, Algebra.smul_def, mul_comm]
  simp

-- lemma 4.9
theorem charFun_GaussianDistribution (μ : ℝ) (v : ℝ≥0 )(t : ℝ ) : charFun (Gaussian_Distribution μ v) (t) = exp (μ * t * I - (v * t)^2 / 2) := by
  simp[charFun]
  rw[gaussian_integral_var_change μ v t (fun x => exp (↑t * ↑x * I))]
  simp[gaussianPdf]
  sorry


lemma charFun_eq_fourierIntegral_Euler (μ : Measure E) (t : E) (hf : Integrable (fun x ↦ cos ⟪t, x⟫) μ) (hg : Integrable (fun x ↦ (sin ⟪t, x⟫) * I) μ ):
    charFun μ t = ∫ a, cos (⟪t, a⟫) ∂μ + (∫ a,(sin (⟪t, a⟫)) • I ∂μ) := by
    simp [charFun , exp_mul_I]
    rw [integral_add]
    exact hf
    exact hg

@[simp]
lemma charFun_zero (μ : Measure E) [IsProbabilityMeasure μ] : charFun μ 0 = 1 := by
  simp only [charFun, inner_zero_left, zero_smul,exp_zero, integral_const, measure_univ,
  ENNReal.one_toReal, one_smul]
--lemma 4.4
lemma charFun_neg (μ : Measure E) (t : E) : charFun μ (-t) = conj (charFun μ t) := by
  simp [charFun, ← integral_conj, ← exp_conj, conj_ofReal]


-- lemma 4.2
lemma norm_charFun_le_one (μ : Measure E) [IsProbabilityMeasure μ] (t : E) : ‖charFun μ t‖ ≤ 1 := by
  rw [charFun_eq_fourierIntegral]
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans_eq ?_
  --被积项的不等号
  simp only [CstarRing.norm_one, integral_const, smul_eq_mul, mul_one, measure_univ, ENNReal.one_toReal]

-- lemma 4.5
lemma charFun_ofvariable_lin (X : Ω → ℝ) (_ℙ : Measure Ω) (a b : ℝ) (t : ℝ)[NormedAddCommGroup Ω][NormedAddCommGroup ℝ](μ : Measure ℝ) [HasPDF X _ℙ μ]:
    charFun_of (fun x => a * X x + b) _ℙ t = (charFun_of X _ℙ (t * a)) * exp (I * b * t) := by
  simp [charFun_of, charFun_ofvariable, mul_add, add_mul, mul_assoc, exp_add]
  rw [integral_mul_right]
  congr 2
  ring

theorem IndepFun.integral_mul'' (X : Ω → ℂ) (Y : Ω → ℂ) (hXY : IndepFun X Y μ) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) : integral μ (X * Y) = integral μ X * integral μ Y := by
  sorry

-- lemma 4.6
lemma charFun_of_add_indep (X : Ω → ℝ) (Y : Ω → ℝ) (_ℙ : Measure Ω) (t : ℝ) (indep : IndepFun X Y _ℙ):
    charFun_of (X + Y) _ℙ t = (charFun_of X _ℙ t) * (charFun_of Y _ℙ t) := by
    simp [charFun_of]
    simp only [mul_add, add_mul, Complex.exp_add]
    apply IndepFun.integral_mul''
    sorry
    sorry
    sorry

-- lemma 4.8
lemma difference_of_charFun (X : Ω → ℝ) (_ℙ : Measure Ω) (a b : ℝ):
    ‖(charFun_of X _ℙ a) - (charFun_of X _ℙ b)‖ ≤ 2 * ∫ (x : Ω) , min |( s - t )*(X x)| 1 ∂_ℙ := by
    simp [charFun_of]
    have h₁ : MeasureTheory.Integrable (fun x => cexp (↑a * ↑(X x) * I)) := by sorry
    have h₂ : MeasureTheory.Integrable (fun x => cexp (↑b * ↑(X x) * I)) := by sorry
    sorry


-- below definitions are for lemma 5.1, including higher order derivs and a C to C version of charFun_of
noncomputable
def rpow_func (X : Ω → ℝ) (n : ℕ): Ω → ℝ := fun x => Real.rpow (X x) n
noncomputable
def cpow_func (X : Ω → ℂ) (n : ℕ): Ω → ℂ := fun x => Complex.cpow (X x) n

noncomputable
def deriv_func (f : ℂ → ℂ): ℂ → ℂ := fun x => deriv f x
noncomputable
def nth_deriv (f : ℂ → ℂ) (n : ℕ) (x : ℝ): ℂ := Nat.iterate (deriv_func f) n x

noncomputable
def charFun_of_CtoC (X : Ω → ℝ) (_ℙ : Measure Ω) (t : ℝ) : ℂ → ℂ :=
  let _ : ℂ := Complex.mk t 0;
  fun _ => ∫ (x : Ω), exp (⟪t, X x⟫ • I) ∂_ℙ

def I_times_func (X :  Ω → ℝ) : Ω → ℂ := fun x => I * (X x)

-- lemma 5.1
lemma deriv_charFun (X : Ω → ℝ) (_ℙ : Measure Ω) (t : ℝ) (k n : ℕ)
(n_mom_bd: ∃ c : ℝ, MeasureTheory.integral _ℙ  (rpow_func |X| n) ≤ c )(le: k ≤ n):
    nth_deriv (charFun_of_CtoC X _ℙ t) k t =
    MeasureTheory.integral _ℙ ((cpow_func (I_times_func X) k) * (fun x => exp (I * t * X x)))
    := by
    sorry

--lemma 4.3
lemma charFun_continuous [Inner ℝ E] (X : Ω → E) (_ℙ : Measure Ω) (t : E):
    Continuous fun t => charFun_of X _ℙ t:= by
    dsimp [charFun_of]
    sorry

-- CLT
theorem CLT (X_seq : ℕ → (Ω → ℝ)) (_ℙ : Measure Ω) (Z: Ω → ℝ) (Z_law: Measure.map Z _ℙ = Gaussian_Distribution 0 1)
(X_par: ℕ → Ω → ℝ:= fun n => (1 / Nat.sqrt n) * (Finset.sum (Finset.range n) (X_seq)))
(iid: ∀ i j : ℕ, IndepFun (X_seq i) (X_seq j) _ℙ ∧ Measure.map (X_seq i) _ℙ = Measure.map (X_seq j) _ℙ)
(X_seq_prop: ∀ i : ℕ, MeasureTheory.integral _ℙ (X_seq i) = 0 ∧ ProbabilityTheory.variance (X_seq i) _ℙ = 1):
    1 = 1 := by
    sorry  -- need to fill in 'X_par converges to Z in distribution' as the goal

end ProbabilityTheory
