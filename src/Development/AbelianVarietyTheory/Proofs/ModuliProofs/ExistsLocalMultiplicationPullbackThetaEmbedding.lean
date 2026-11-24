module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddingSectionsSpanGeometricFibreStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGenSecNear
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbeddingI
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MonoOfGeomPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjCoordRepresentationGeometricFibreSpanningStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffineStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.EmbedLocal

theorem exists_emb_projRep :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh x v → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ ∧ ProjRep (idealOf (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ (𝟙 _)) (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ :=
  of_parts GlobalTheory.exists_emb_locally GlobalTheory.T.thetaEmbeddingSections_baseChange_affine GlobalTheory.T.embedding_sections_span_geometric_fibre GlobalTheory.T.projCoordRepresentation_geometric_fibre_spanning GlobalTheory.FibreEmbed.projRep_of_fibres

end GlobalTheory.ZM.EmbedLocal
