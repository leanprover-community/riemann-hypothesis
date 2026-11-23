module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordinaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocyclesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomEvalTwoVariableSeries
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

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.rig_pull_natural_semi : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (φ : Fin d → MvPowerSeries (Fin e) k') (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] ((G'.cocycles × G'.omega) ⧸ _root_.LinearMap.range (G'.cob.prod (_root_.LinearMap.codRestrict G'.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G'.A i))).domRestrict G'.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (t, w) = G.rigMk (z, u)) → (∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k') (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u)) → ∀ t w, IsCoc μ t → ρ' (pull2 φ (MvPowerSeries.map σ t), pullLin φ (fun i => σ (w i))) = s.rig (ρ (t, w)) := by
  intro p k k' _ _ σ d e G G' c c' s μ φ ρ ρ' hμ hφ hρ hρ' t w ht
  have hz : (fun n => c.ev₂ n t) ∈ G.cocycles := (GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ t).1 ht
  have hu : (fun n => ∑ i, w i • dUnit (R := k) (c.x n i)) ∈ G.omegaSub := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1 w
  rw [hρ t w ⟨_, hz⟩ ⟨_, hu⟩ (fun _ => rfl) (fun _ => rfl), SemiHom.rig_mk]
  have hev : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
    intro n
    exact GlobalTheory.Katz.semiHom_ev₂_pull2 p k k' σ d e G G' c c' s φ hφ n t
  refine hρ' _ _ _ _ (fun n => ?_) (fun n => ?_)
  · rw [SemiHom.cocycles_val, hev n]
  · rw [SemiHom.omega_val]
    change (s.app n).cot (∑ i, w i • dUnit (R := k) (c.x n i)) = _

    rw [map_sum]
    simp only [map_smulₛₗ, SemiBialgHom.cot_d]
    have hd : ∀ i, dUnit (R := k') (s.app n (c.x n i)) = ∑ l, lin (φ i) l • dUnit (R := k') (c'.x n l) := fun i => by
      rw [← hφ n i]
      exact (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k' e (G'.A n) (c'.x n) (c'.nil n) (c'.aug n) (φ i)).2
    simp only [hd, Finset.smul_sum, smul_smul, pullLin, Finset.sum_smul]
    exact Finset.sum_comm
