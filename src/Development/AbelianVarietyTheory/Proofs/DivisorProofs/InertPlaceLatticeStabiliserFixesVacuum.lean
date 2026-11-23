module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSelfDualLatticeFixedFunctionsLineStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabilizerVacuumEigenvalueEqOneInertPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuuStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVWStatement
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

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem vac_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk
  obtain ⟨hSB, hne, θ, hθ, hfix⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hT v k hk.1 _ hSB
  have hfix₁ := GlobalTheory.T.weilOperator_latticeStabiliser_right_preserves_vacuumType F E σ B a a' G X om om' hT v k hk θ hθ _ hSB φ₁ hφ₁ hfix hact
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line F E σ B a a' G X om om' hT v (hT.base.inert v w hin).2.2
    (GlobalTheory.T.tensorLattice_inertPlace_selfDual F E σ B a a' G X om om' hT v w hin) θ hθ _ hSB hne hfix φ₁ hφ₁ hfix₁
  have hc := GlobalTheory.T.latticeStabilizer_vacuum_eigenvalue_eq_one_inertPlace F E σ B a a' G X om om' hT v w hin hvT k hk c hact
  rw [hc, one_smul] at hact
  exact hact

end GlobalTheory.InertSph
