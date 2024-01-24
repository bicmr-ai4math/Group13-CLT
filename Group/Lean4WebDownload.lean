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
variable {Ω : Type*} [MeasurableSpace Ω]

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

-- one 'sorry' needed to be clear
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

lemma charFun_neg (μ : Measure E) (t : E) : charFun μ (-t) = conj (charFun μ t) := by
  simp [charFun, ← integral_conj, ← exp_conj, conj_ofReal]



lemma norm_charFun_le_one (μ : Measure E) [IsProbabilityMeasure μ] (t : E) : ‖charFun μ t‖ ≤ 1 := by
  rw [charFun_eq_fourierIntegral]
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans_eq ?_
  --被积项的不等号
  simp only [CstarRing.norm_one, integral_const, smul_eq_mul, mul_one, measure_univ, ENNReal.one_toReal]


lemma charFun_ofvariable_lin (X : Ω → ℝ) (_ℙ : Measure Ω) (a b : ℝ) (t : ℝ)[NormedAddCommGroup Ω][NormedAddCommGroup ℝ](μ : Measure ℝ) [HasPDF X _ℙ μ]:
    charFun_of (fun x => a * X x + b) _ℙ t = (charFun_of X _ℙ (t * a)) * exp (I * b * t) := by
  simp [charFun_of, charFun_ofvariable, mul_add, add_mul, mul_assoc, exp_add]
  sorry

lemma charFun_of_add_indep (X : Ω → ℝ) (Y : Ω → ℝ) (_ℙ : Measure Ω) (t : ℝ) (indep : IndepFun X Y _ℙ):
    charFun_of (X + Y) _ℙ t = (charFun_of X _ℙ t) * (charFun_of Y _ℙ t) := by
    sorry

end ProbabilityTheory
