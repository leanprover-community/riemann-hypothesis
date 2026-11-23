module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnifStatement
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import GroundTheory.HeightsAndTheta.Heights.HermitianTensor

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem rank_eq_unif_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (M : LB A.left) (g : ℕ) (u : HolUnif A M g), IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → D.g = g := by
  intro E _ _ _ H L _ _ D σ A _ φ M g u hp h1 h2
  haveI : Smooth D.t.G.hom := D.t.semi.smooth
  obtain ⟨Mσ, -⟩ := GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre (Sp (𝓞 L)) D.t.G L (𝟙 _) D.B.carrier D.MB σ
  have hp' : IsGrpPullback A D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) φ := by
    rwa [Category.comp_id]
  obtain ⟨e, -⟩ := GlobalTheory.T.tangent_space_equiv_hol_unif _ D.t.G _ _ Mσ A φ M g u hp' h1 h2
  have hf : Module.finrank ℂ (Fibre σ D.B.carrier) = g := by
    rw [e.finrank_eq, Module.finrank_fin_fun]
  have hr : Module.finrank ℂ (FibreSpace D.B.metric σ) = Module.finrank (𝓞 L) D.B.carrier :=
    GroundTheory.Heights₂.Heights.FibreMahlerForms.finrank_fibreSpace D.B.metric σ
  have hq : Module.finrank ℂ (FibreSpace D.B.metric σ) = Module.finrank ℂ (Fibre σ D.B.carrier) :=
    (FibreSpace.equiv D.B.metric σ).symm.finrank_eq
  change Module.finrank (𝓞 L) D.B.carrier = g
  rw [← hr, hq, hf]

end GlobalTheory.CompanionTheory.Ar.Sl
