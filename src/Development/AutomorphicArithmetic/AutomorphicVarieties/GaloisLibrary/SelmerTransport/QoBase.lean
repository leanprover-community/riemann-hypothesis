module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelBase
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelBaseEig
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.qoBase :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (χ : G →* ℤ_[l]ˣ) (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O (LocSel (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ)) U 𝒟) = Module.length ℤ_[l] (LocSel (scalRep (QZ l) χ) U 𝒟) * eO l O ∧
      ∀ [U.Normal] (h𝒟 : ConjStable 𝒟) (g : G) (s : ℤ_[l]),
        Module.length O (Module.End.eigenspace (selRep (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ)) U h𝒟 g) (algebraMap ℤ_[l] O s)) =
          Module.length ℤ_[l] (Module.End.eigenspace (selRep (scalRep (QZ l) χ) U h𝒟 g) s) * eO l O := by
  intro l _ G _ _ _ O _ _ _ _ _ χ U 𝒟
  obtain ⟨-, hfree, hloc, -, he, -⟩ := dvrFacts l O
  have hj : ∀ g m, QO.incl l O (scalRep (QZ l) χ g m) =
      twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ) g (QO.incl l O m) := fun g m => by
    show QO.incl l O (((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m) = algebraMap ℤ_[l] O (χ g : ℤ_[l]ˣ) • QO.incl l O m
    rw [map_smul, algebraMap_smul]
  rw [he]
  exact ⟨selBase ℤ_[l] G (QZ l) (scalRep (QZ l) χ) O (QO l O) _ (QO.incl l O) (QO.isBaseChange l O) hj U 𝒟,
    fun h𝒟 g s => (selBaseEig ℤ_[l] G (QZ l) (scalRep (QZ l) χ) O (QO l O) _ (QO.incl l O)
      (QO.isBaseChange l O) hj U 𝒟 h𝒟).2 g s⟩
