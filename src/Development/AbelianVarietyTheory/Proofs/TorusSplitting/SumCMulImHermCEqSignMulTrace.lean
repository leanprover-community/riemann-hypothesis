module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory


open NumberField in
theorem _root_.GlobalTheory.re_map_xi_eq_zero {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : E →+* ℂ) : (τ X.ξ0).re = 0 := by
  have h := congrArg τ X.ξ0_im
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg] at h
  have h2 := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at h2
  linarith


open NumberField in
theorem _root_.GlobalTheory.c_eq_two_mul_abs_im {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r : ℕ}
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : X.Ψ) : X.c τ = 2 * |(τ.1 X.ξ0).im| := by
  have hre := _root_.GlobalTheory.re_map_xi_eq_zero X τ.1
  have hz : τ.1 X.ξ0 = ((τ.1 X.ξ0).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.c
  conv_lhs => rw [hz]
  simp [Complex.norm_real]

end GlobalTheory
