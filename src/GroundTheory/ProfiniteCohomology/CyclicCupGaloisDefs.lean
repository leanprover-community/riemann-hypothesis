module

public import GroundTheory.ProfiniteCohomology.Characters
public import GroundTheory.ProfiniteCohomology.CupProducts
public import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

section Generic

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

noncomputable def cupRightProf (h : p + q = n) (b : cohomology B q) :
    cohomology A p ⟶ cohomology (A ⊗ B) n :=
  ModuleCat.ofHom ((cup h).flip b)

theorem cupRightProf_apply (h : p + q = n) (b : cohomology B q) (a : cohomology A p) :
    (cupRightProf h b).hom a = cup h a b :=
  rfl

end Generic

section Profinite

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

noncomputable def charClassProf (χ : Additive G →ₜ+ QZ) : cohomology (Rep.trivial ℤ G ℤ) 2 :=
  (δ (GroundTheory.GroupCoh.ratSES_shortExact G) 1 2 rfl).hom ((cohomologyOneRatModIntIso G).inv.hom χ)

noncomputable def cupCharClassProf (A : Rep ℤ G) [IsDiscreteRep A] (χ : Additive G →ₜ+ QZ) :=
  (H0Iso A).inv ≫ cupRightProf (A := A) (B := Rep.trivial ℤ G ℤ) (zero_add 2) (charClassProf χ) ≫
    cohomologyMap (A := A ⊗ Rep.trivial ℤ G ℤ) (B := A) (ρ_ A).hom 2

end Profinite

section Galois

variable (K L : Type) [Field K] [Field L] [Algebra K L]

def unitsInvariant (a : Kˣ) : (galUnitsZ K L).ρ.invariants :=
  ⟨Additive.ofMul (Units.map (algebraMap K L : K →* L) a), fun σ => by
    apply Additive.toMul.injective
    apply Units.ext
    change ((galUnitsHom K L σ (Units.map (algebraMap K L : K →* L) a) : Lˣ) : L) =
      (Units.map (algebraMap K L : K →* L) a : L)
    rw [coe_galUnitsHom_apply]
    simp⟩

@[simp]
theorem coe_unitsInvariant (a : Kˣ) :
    ((Additive.toMul (unitsInvariant K L a : Additive Lˣ) : Lˣ) : L) = algebraMap K L a :=
  rfl

variable [IsGalois K L]

noncomputable def galCupClass (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) :
    cohomology (galUnitsZ K L) 2 :=
  (cupCharClassProf (galUnitsZ K L) χ).hom (unitsInvariant K L a)

end Galois

end GroundTheory.ProfCoh
