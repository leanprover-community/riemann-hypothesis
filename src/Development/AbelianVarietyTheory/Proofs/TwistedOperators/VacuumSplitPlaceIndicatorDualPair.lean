module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumEigenvalueEqOneSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuu
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
import GroundTheory.GlobalFields.LocalFieldAtPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SplitParLeft

open GlobalTheory.DblVacLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem chr_det_eq_one {n : ℕ} (Y : Spc F E n) (hL : Y.L.IsFullLattice E) (v : Pl (F := F)) (χ : Chr F E)
    (hχ : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) (t : GL (Fin n) (AE F E))
    (h1 : At (evFin F v) ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1))
    (h2 : ∀ z ∈ GlobalTheory.InertSph.latAt Y v, (t : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt Y v ∧
      ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt Y v) :
    χ (Matrix.GeneralLinearGroup.det t) = 1 := by
  first | exact _root_.GlobalTheory.DblVacSiegelAny.chr_det_eq_one_any | exact @_root_.GlobalTheory.DblVacSiegelAny.chr_det_eq_one_any | apply _root_.GlobalTheory.DblVacSiegelAny.chr_det_eq_one_any <;> assumption

theorem dblFun_eigen_left {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} (hB : B.IsGood σ) (hG : G.IsGood B)
    (v : Pl (F := F)) (hunr : PsiUnr B.ψ v)
    (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a')))
    (hd' : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x)
    (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
    (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ))
    (hdc : IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd)
    (hS : IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd)
    (R : (Fin a' × Fin (a + a') → AF F) → ℂ) (hR : Rest (evFin F v) (G.M'.vac v) R)
    (g : GlobalTheory.InertDbl.UD σ G.V') (hg : g ∈ GlobalTheory.InertDbl.KAtD σ G.V' v) :
    ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  obtain ⟨hSB, h0, θ, -, hvac⟩ := hG.hM'.vac v
  have hsd := GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V' G.W _ _ _ _ hB hG.hV' hG.hW v
  refine dbl_line_coord hB.std v hunr hG.hW.lat.toIsLattice hG.hV'.lat.toIsLattice (fun z hz => ?_) d' _ hSB h0 (θ : E) (fun γ hγ => ?_)
    dd omd hdc hS R hR g hg
  · have hzt : At (evFin F v) zᵀ := fun u hu => by
      rw [← Matrix.transpose_smul, hz u hu, Matrix.transpose_zero]
    constructor
    · intro hm γ hγ
      rw [← GlobalTheory.WeilSchrodinger.symp_transpose]
      exact (hsd _ hzt).1 (GlobalTheory.AdelMatLatRight.transpose_mem_latAtV _ _ v z hm) _
        (GlobalTheory.AdelMatLatRight.transpose_mem_latAtV _ _ v γ hγ)
    · intro hm
      refine GlobalTheory.AdelMatLatRight.transpose_mem_latAtV _ _ v zᵀ ((hsd _ hzt).2 fun γ hγ => ?_)
      have := hm _ (GlobalTheory.AdelMatLatRight.transpose_mem_latAtV _ _ v γ hγ)
      rwa [← GlobalTheory.WeilSchrodinger.symp_transpose, Matrix.transpose_transpose] at this
  · have h := hvac _ (GlobalTheory.AdelMatLatRight.transpose_mem_latAtV _ _ v γ hγ)
    have e : d'.rho B.ψ γ = G.M'.co.rho B.ψ γᵀ := by
      simp only [Darboux.rho, ← hd', Matrix.transpose_transpose]
    rw [GlobalTheory.WeilSchrodinger.symp_transpose, ← e] at h
    exact h

end GlobalTheory.SplitParLeft

end
