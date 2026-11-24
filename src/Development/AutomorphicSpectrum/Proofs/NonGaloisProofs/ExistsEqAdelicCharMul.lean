module

public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

namespace GlobalTheory.CompanionTheory.AdeleDual

open GroundTheory.Global

variable {F : Type} [Field F] [NumberField F]

theorem exists_eq_adelicChar_mul (χ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hc : Continuous χ)
    (hF : ∀ a : F, χ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) :
    ∃ ξ : F, ∀ x, χ x = (adelicChar F (algebraMap F (AdeleRing (𝓞 F) F) ξ * x) : ℂ) := by
  have hn := GlobalTheory.CompanionTheory.AdeleAnn.norm_eq_one χ hc hF
  let χ' : AddChar (AdeleRing (𝓞 F) F) Circle :=
    { toFun := fun y => ⟨χ y, mem_sphere_zero_iff_norm.2 (hn y)⟩
      map_zero_eq_one' := Circle.ext (by simp)
      map_add_eq_mul' := fun a b => Circle.ext (χ.map_add_eq_mul a b) }
  have hχ' : Continuous χ' := hc.subtype_mk _
  obtain ⟨ξ, hξ, -⟩ := GroundTheory.Global.existsUnique_eq_adelicChar_mul χ' hχ' fun k => Circle.ext (hF k)
  exact ⟨ξ, fun x => congrArg (fun c : Circle => (c : ℂ)) (hξ x)⟩

end GlobalTheory.CompanionTheory.AdeleDual
