module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.KappaLatticeEvaluation
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section


open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.LatAllFG

theorem fg_latOf_congr {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] {C C' : Submodule K R} (hC : C = C')
    (Vs : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (h : (latOf C Vs hV).FG) : (latOf C' Vs hV).FG := by
  subst hC; exact h

theorem latW_fg {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (hn : 0 < w.n) :
    (latW (T.U j) (wtZ (wtA w) w.n)).FG := by
  have h := (GlobalTheory.SupFull.fullAt_of_pins D T.toCore hT.pins j hj (hT.unf j hj _ T.good_σ₀) w hn).1
  unfold GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation.supLat GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation.latIn at h
  have h2 := Submodule.fg_of_fg_map_injective _ Subtype.val_injective h
  exact fg_latOf_congr (cuspW_wtZ (Xo := T.Q.Xo j) (c := T.Q.c) (U := T.U j) (wtA w) w.n).symm _ _ h2

theorem fg_span_image {K L V W : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module L W] [Module (𝓞 L) W] [IsScalarTower (𝓞 L) L W]
    (ι : V →ₛₗ[algebraMap K L] W) (M : Submodule (𝓞 K) V) (hM : M.FG) :
    (Submodule.span (𝓞 L) (ι '' (M : Set V))).FG := by
  classical
  obtain ⟨s, hs⟩ := hM
  refine ⟨s.image ι, le_antisymm ?_ ?_⟩
  · rw [Finset.coe_image]
    exact Submodule.span_mono (Set.image_mono (hs ▸ Submodule.subset_span))
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have e : ι (c • y) = (RingOfIntegers.mapRingHom (algebraMap K L) c) • ι y := by
        rw [← algebraMap_smul K c y, ι.map_smulₛₗ, ← algebraMap_smul L (RingOfIntegers.mapRingHom (algebraMap K L) c) (ι y)]
        rfl
      rw [e]
      exact Submodule.smul_mem _ _ hy

end GlobalTheory.CovTop.LatAllFG

