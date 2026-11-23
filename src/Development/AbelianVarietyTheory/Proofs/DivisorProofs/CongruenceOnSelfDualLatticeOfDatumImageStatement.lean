module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeOfDatumImage
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

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.congruence_on_selfDual_lattice_of_datum_image : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}, LatEmb V ι → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ a : La, ∃ w ∈ latGHat V 1, t • (K *ᵥ finVec V (ι a) - finVec V (ι a)) = M • w) → ∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y := by
  first | exact @GlobalTheory.LevelLatticeCong.cong_on_sdLattice | exact GlobalTheory.LevelLatticeCong.cong_on_sdLattice | (intros; apply GlobalTheory.LevelLatticeCong.cong_on_sdLattice <;> assumption)
