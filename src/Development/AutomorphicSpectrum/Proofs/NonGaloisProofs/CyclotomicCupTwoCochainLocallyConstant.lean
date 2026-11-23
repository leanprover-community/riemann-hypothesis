module

public import Formalism.GaloisCohomology.LocalTateDualityK
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.TopCoh

open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift

theorem coboundary_of_characters (hT : LocalTateDualityK) (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (hK : FiniteDimensional ℚ_[l] K) (n : ℕ) (hn : 0 < n)
    (hχ : Continuous fun g => ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (z : Formalism.GaloisCohomology.GK l K × Formalism.GaloisCohomology.GK l K → M) (hz : Continuous z)
    (hcoc : ∀ g h k, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • z (h, k) - z (g * h, k) +
      z (g, h * k) - z (g, h) = 0)
    (hchar : ∀ ψ : M →+ ZMod (l ^ n), ∃ f : Formalism.GaloisCohomology.GK l K → ZMod (l ^ n), Continuous f ∧
      ∀ g h, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * f h - f (g * h) + f g = ψ (z (g, h))) :
    ∃ f : Formalism.GaloisCohomology.GK l K → M, Continuous f ∧
      ∀ g h, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • f h - f (g * h) + f g = z (g, h) := by
  let rho : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K) M := scalRep M (cycK l K n)
  have hrho : ContAction rho :=
    (continuous_of_discreteTopology (f := fun q : ZMod (l ^ n) × M => q.1 • q.2)).comp
      ((hχ.comp continuous_fst).prodMk continuous_snd)
  have hz2 : z ∈ Z2 (rho.comp (MonoidHom.id _)) := ⟨hz, hcoc⟩
  have hb := (hT l K hK n M rho hn hrho).2.2.2.2
  have hzero : cup20 (cycK l K n) rho (MonoidHom.id _) (Submodule.Quotient.mk ⟨z, hz2⟩) = 0 := by
    refine LinearMap.ext fun φ => ?_
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    let φ' : M →ₗ[ZMod (l ^ n)] ZMod (l ^ n) := φ.1
    obtain ⟨f, hf, hd⟩ := hchar φ'.toAddMonoidHom
    exact ⟨f, hf, funext fun p => hd p.1 p.2⟩
  have h0 := hb.1 (hzero.trans (map_zero _).symm)
  obtain ⟨c, hc, hd⟩ := (Submodule.Quotient.mk_eq_zero _).1 h0
  exact ⟨c, hc, fun g h => congrFun hd (g, h)⟩

end GlobalTheory.CompanionTheory.LocDual.TopCoh
