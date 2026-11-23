module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoOfDisjointCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

def openRatModel {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k) (U : X.Opens) [IsIntegral U.toScheme]
    (hsep : IsSeparated s) (hlft : LocallyOfFiniteType s) (hqc : QuasiCompact (U.ι ≫ s)) :
    letI : Algebra k U.toScheme.functionField :=
      (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
    RatModel k U.toScheme.functionField :=
  letI : Algebra k U.toScheme.functionField :=
    (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
  { Z := U.toScheme
    s := U.ι ≫ s
    sep := inferInstance
    lft := inferInstance
    qc := hqc
    pt := U.toScheme.fromSpecStalk (genericPoint U.toScheme)
    pt_s := by
      unfold spMap
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
    gen := by
      refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, Scheme.fromSpecStalk_closedPoint⟩, ?_⟩
      rintro _ ⟨w, rfl⟩
      have : w = IsLocalRing.closedPoint U.toScheme.functionField :=
        Subsingleton.elim (α := PrimeSpectrum U.toScheme.functionField) _ _
      rw [this]
      exact Scheme.fromSpecStalk_closedPoint
    onto := fun x => by
      obtain ⟨V, h, a, rfl⟩ := U.toScheme.presheaf.germ_exist (x := genericPoint U.toScheme) x
      exact ⟨V, a, ⟨_, h⟩, GlobalTheory.FlagBundle.valF_fromSpecStalk h a⟩ }

theorem lbIso_of_ratModels : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (s : X ⟶ Sp k) (A B : LB X), Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → A.IsLB → B.IsLB → (∀ (Ω : Type) [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (io : M.Z ⟶ X), IsOpenImmersion io → io ≫ s = M.s → LBIso (A.pull io) (B.pull io)) → LBIso A B := by
  intro k _ _ X s A B hN hsep hlft hqc hA hB hM
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  refine GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover X (irreducibleComponents X) GlobalTheory.IsNormalScheme.component
    (fun a b y ha hb => Subtype.ext (GlobalTheory.IsNormalScheme.eq_of_mem_irreducibleComponents a.2 b.2 ha hb))
    (fun y => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents y⟩, mem_irreducibleComponent⟩) A B hA hB ?_
  intro Z
  let U := GlobalTheory.IsNormalScheme.component Z
  letI : Algebra k U.toScheme.functionField :=
    (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
  have hio : IsOpenImmersion U.ι := by infer_instance
  exact hM _ (openRatModel s U hsep hlft inferInstance) U.ι hio rfl

end GlobalTheory.UMin
