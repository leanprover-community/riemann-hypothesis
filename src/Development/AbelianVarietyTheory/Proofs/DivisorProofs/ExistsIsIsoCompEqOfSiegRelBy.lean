module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.SiegFactor

theorem comp_id_pow {S : Scheme.{0}} {T A : Over S} [GrpObj A] (x : T ⟶ A) (k : ℕ) :
    x ≫ (𝟙 A) ^ k = x ^ k := by
  rw [MonObj.comp_pow, Category.comp_id]

theorem id_pow_comp {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (χ : A ⟶ B) [IsMonHom χ]
    (k : ℕ) : ((𝟙 A) ^ k) ≫ χ = χ ≫ (𝟙 B) ^ k := by
  rw [MonObj.pow_comp, Category.id_comp, comp_id_pow]

theorem isMonHom_epi_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {k : ℕ}
    (hk : 0 < k) : IsMonHom ((𝟙 A) ^ k) ∧ Epi ((𝟙 A) ^ k) := by
  have := hA.comm
  have hm : IsMonHom ((𝟙 A) ^ k) := GlobalTheory.AbLaw.MulN.isMonHom_mulA A k
  obtain ⟨hfl, hsu, hqc⟩ := SiegUniqBase.flat_surjective_qc_pow S A hA k hk
  exact ⟨hm, (GlobalTheory.exists_monHom_factor_of_flat_surjective S A A A _ _ hm hm hfl hsu hqc
    fun _ _ h => h).2⟩

end GlobalTheory.UPel.HT.SiegFactor

namespace GlobalTheory.UPel.HT

end GlobalTheory.UPel.HT
