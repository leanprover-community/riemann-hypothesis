module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GenericSectionOfAxioms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAG

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_lattice (hd : d.AxH 𝒜) (h : d.S1) :
    d.De hd h ≠ 0 ∧ ∀ la, (d.htOf hd h).Ila la ≠ ⊤ ∧
      2 * d.IL h hd.sel hd.a4.choose la ≤
        d.gOrd la (d.De hd h) + 2 * d.NlaG h d.wF hd.a4.choose la := by
  have key : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (d.htOf hd h).Ila la ≠ ⊤ ∧ d.De hd h ≠ 0 ∧
      2 * d.IL h hd.sel hd.a4.choose la ≤
        d.gOrd la (d.De hd h) + 2 * d.NlaG h d.wF hd.a4.choose la := by
    intro la
    obtain ⟨n, t, N, hI, hN, u, hu, hDe⟩ := d.disc_at hd h la
    have hIL : d.IL h hd.sel hd.a4.choose la = (((d.htOf hd h).Ila la).toNat : ℝ) := rfl
    refine ⟨by rw [hI]; exact ENat.coe_ne_top n, ?_, ?_⟩
    · rw [hDe, algK_unif]
      exact mul_ne_zero (zpow_ne_zero _ ((map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr
        (unifOp_irreducible d.D d.N la).ne_zero))
        ((map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr hu.ne_zero)
    · rw [hIL, hI, d.gOrd_eq la hu hDe, hN, ENat.toNat_natCast]
      push_cast
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      linarith
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  let la0 : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField K)⟩
  exact ⟨(key la0).2.1, fun la => ⟨(key la).1, (key la).2.2⟩⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
