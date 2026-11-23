module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondCoordinateOfOrthogonalSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTensorLatticeSelfDualStatement
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
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.SplitSphLeft

theorem vac_unique_split_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M.vac v))) →
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) →
        ∃ c : ℂ, φ = c • G.M.vac v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v hs hψv θ _ hvac φ hφ hfix
  classical
  have hat : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  let cf : latAtV G.V G.W v → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ)
  have hloc : ∀ f ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (G.M.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • f)) →
      ∀ γ : latAtV G.V G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) f = cf γ • f := by
    intro f hf h γ
    exact GlobalTheory.TensUniq.eq_of_tens_eq v f _ _ hf fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ (hat γ γ.2) f r hr).symm.trans (h γ γ.2 r hr)
  have hsd : ∀ z, z ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v) ↔
      ∀ l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v), GlobalTheory.LatVac.psiAt B.ψ v (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1 :=
    GlobalTheory.LatVac.DualLoc.map_selfDual v G.M.co B.ψ (latAtV G.V G.W v) hat
      (fun z hz => GlobalTheory.T.splitPlace_tensorLattice_selfDual F E σ B hTr.base G.V G.W _ _ _ _ hTr.geo.hV hTr.geo.hW v hs hψv z hz)
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v),
      t • l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v) := by
    rintro t ht _ ⟨γ, hγ, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • γ, (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).2 t ht γ hγ, ?_⟩
    rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hbd : ∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ (latAtV G.V G.W v).map (GlobalTheory.LatVac.locCo G.M.co v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F := by
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V G.W v G.M.co hTr.geo.hV.lat.toIsLattice hTr.geo.hW.lat.toIsLattice
    exact ⟨c, hc0, by rintro _ ⟨γ, hγ, rfl⟩ i; exact (hc γ hγ i).1⟩
  have hD := GlobalTheory.T.exists_second_coordinate_of_orthogonal_selfDual v (GlobalTheory.LatVac.psiAt B.ψ v) _ hsd hst hbd
  refine GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun γ : latAtV G.V G.W v => GlobalTheory.LatVac.locCo G.M.co v γ) cf
    (fun u hu => ?_) φ (G.M.vac v) (hloc φ hφ hfix) (hloc _ (hTr.geo.hM.vac v).1 hvac) (hTr.geo.hM.vac v).2.1
  obtain ⟨y', γ, hγ, he⟩ := hD u (by
    rintro y ⟨γ, hγ, he⟩
    have h1 := hu ⟨γ, hγ⟩ (congrArg Prod.fst he)
    have h2 : (GlobalTheory.LatVac.locCo G.M.co v γ).2 = y := congrArg Prod.snd he
    simp only at h1
    rw [h2] at h1
    exact h1)
  exact ⟨⟨γ, hγ⟩, congrArg Prod.fst he⟩

theorem isUnram_of_unramified' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
  intro P hP
  rw [Ideal.ramificationIdx_eq_one_iff]
  infer_instance

end GlobalTheory.SplitSphLeft
