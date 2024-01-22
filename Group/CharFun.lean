/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Probability.Notation
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Init.Order.Defs
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
  map_one' := by simp only; rw [toAdd_one, neg_zero, expMapCircle_zero]
  map_mul' x y := by simp only; rw [toAdd_mul, neg_add, expMapCircle_add]

theorem probFourierChar_apply' (x : ℝ) : probFourierChar[x] = exp (↑(-x) * I) := rfl

theorem probFourierChar_apply (x : ℝ) : probFourierChar[x] = exp (- ↑x * I) := by
  simp only [probFourierChar_apply', ofReal_neg]

@[continuity]
theorem continuous_probFourierChar : Continuous probFourierChar :=
  (map_continuous expMapCircle).comp continuous_toAdd.neg

variable {E : Type _} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℂ E]

theorem fourierIntegral_probFourierChar_eq_integral_exp {V : Type _} [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace V] {W : Type _} [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (μ : Measure V) (f : V → E) (w : W) :
    VectorFourier.fourierIntegral probFourierChar μ L f w =
      ∫ v : V, exp (↑(L v w) * I) • f v ∂μ := by
  simp_rw [VectorFourier.fourierIntegral, probFourierChar_apply, ofReal_neg, neg_neg]

end character

open scoped ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- The characteristic function of a measure. -/
noncomputable
def charFun [Inner ℝ E] (μ : Measure E) (t : E) : ℂ := ∫ x, exp (⟪t, x⟫ • I) ∂μ

noncomputable
def measure_of_rv (X : E → ℝ) (μ : Measure E) : Measure ℝ := by
  exact Measure.map X μ

noncomputable
def charFun_rv [Inner ℝ E] (X : E → ℝ) (μ : Measure E) (t : ℝ) : ℂ :=
  charFun (measure_of_rv X μ) (t) -- idk what's the problem

def scaled_func (X : E → ℝ) (a : ℝ) : E → ℝ := fun x => a * X x

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma charFun_eq_fourierIntegral (μ : Measure E) (t : E) :
    charFun μ t = VectorFourier.fourierIntegral probFourierChar μ sesqFormOfInner
      (fun _ ↦ (1 : ℂ)) t := by
  simp only [charFun, fourierIntegral_probFourierChar_eq_integral_exp, real_smul, smul_eq_mul,
    mul_one]
  congr

@[simp]
lemma charFun_zero (μ : Measure E) [IsProbabilityMeasure μ] : charFun μ 0 = 1 := by
  simp only [charFun, inner_zero_left, zero_smul, exp_zero, integral_const, measure_univ,
    ENNReal.one_toReal, one_smul]

lemma charFun_neg (μ : Measure E) (t : E) : charFun μ (-t) = conj (charFun μ t) := by
  simp [charFun, ← integral_conj, ← exp_conj, conj_ofReal]
  -- todo: conj_ofReal should be simp

lemma norm_charFun_le_one (μ : Measure E) [IsProbabilityMeasure μ] (t : E) : ‖charFun μ t‖ ≤ 1 := by
  rw [charFun_eq_fourierIntegral]
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans_eq ?_
  simp only [CstarRing.norm_one, integral_const, smul_eq_mul, mul_one, measure_univ,
    ENNReal.one_toReal]

(μ : ℝ)  (v : NNReal) :
ProbabilityTheory.gaussianPDFReal μ v = fun (x : ℝ) =>
  (Real.sqrt (2 * Real.pi * ↑v))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * ↑v))

lemma gaussianPDFReal_positive (μ : ℝ)  (v : NNReal) (x : ℝ): gaussianPDFReal μ v x ≥ 0:= by
  dsimp [gaussianPDFReal]
  have h11 : Real.sqrt 2 > 0 := by norm_num
  have h12 : Real.sqrt Real.pi > 0 := by norm_num; exact Real.pi_pos
  have h13 : Real.sqrt v ≥ 0 := by simp [Real.le_sqrt_of_sq_le]
  have h14 : Real.sqrt 2 * Real.sqrt Real.pi ≥ 0 := by apply le_of_lt (mul_pos h11 h12)
  have h15 : Real.sqrt 2 * Real.sqrt Real.pi * Real.sqrt v ≥ 0 := by exact mul_nonneg h14 h13
  have h1 : Real.sqrt (2 * Real.pi * ↑v) ≥ 0 := by norm_num [h15]
  simp [NNReal.sqrt_pos, NNReal.sqrt_mul, NNReal.sqrt_le_sqrt_iff, mul_pos]
  norm_num



noncomputable
def gaussian_PMF (μ : ℝ)  (v : NNReal) (x : ℝ): PMF ℝ := {
    val:= fun x => gaussianPDFReal μ v x
    property:= simp
}



lemma gaussian_charFun (m : ℝ)  (v : NNReal) (t : ℝ) :
    charFun (gaussianReal m v) (t) = exp (I * t * m - v * t * t / 2) := by
    sorry



lemma charFun_smul (X : E → ℝ) (a t : ℝ) : charFun_rv (scaled_func X a) t = charFun_rv X (a * t) := by
sorry

lemma deriv_charFun

end ProbabilityTheory
