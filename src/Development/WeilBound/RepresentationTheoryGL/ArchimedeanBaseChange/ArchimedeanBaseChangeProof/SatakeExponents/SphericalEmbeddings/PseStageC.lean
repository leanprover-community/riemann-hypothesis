module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.StageLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageA
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGenericOfInjective

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unrChar_append {r t : ℕ} (a : Fin r → ℂˣ) (b : Fin t → ℂˣ) :
    (fun i => unrChar k (Fin.append a b i)) = Fin.append (fun i => unrChar k (a i)) (fun i => unrChar k (b i)) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp


theorem prin_append {r t : ℕ} (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) :
    Nonempty ((prod₂ (prinSeries ψ₁) (prinSeries ψ₂)).Equiv (prinSeries (Fin.append ψ₁ ψ₂))) := by
  obtain ⟨E1⟩ := GlobalTheory.SmGL.PrinProd.stage_one (k := k) ψ₁ ψ₂
  obtain ⟨E2⟩ := GlobalTheory.SmGL.PrinProd.stage_two (k := k) ψ₁ ψ₂
  exact ⟨E1.trans E2⟩


theorem iP_append (r t : ℕ) (A : Fin r → ℂˣ) (B : Fin t → ℂˣ) :
    Nonempty ((prod₂ (iP (k := k) A) (iP (k := k) B)).Equiv (iP (k := k) (Fin.append A B))) := by
  have key : ∀ χ : Fin (r + t) → kˣ →* ℂˣ,
      χ = Fin.append (fun i => unrChar k (A i)) (fun i => unrChar k (B i)) →
      Nonempty ((prod₂ (prinSeries fun i => unrChar k (A i))
        (prinSeries fun i => unrChar k (B i))).Equiv (prinSeries χ)) := by
    rintro χ rfl
    exact prin_append _ _
  exact key _ (unrChar_append A B)

theorem mainGen {r t : ℕ} {VA VB Vc Vc' Vi Vi' Vo Vo' : Type} [AddCommGroup VA] [Module ℂ VA] [AddCommGroup VB]
    [Module ℂ VB] [AddCommGroup Vc] [Module ℂ Vc] [AddCommGroup Vc'] [Module ℂ Vc'] [AddCommGroup Vi] [Module ℂ Vi]
    [AddCommGroup Vi'] [Module ℂ Vi'] [AddCommGroup Vo] [Module ℂ Vo] [AddCommGroup Vo'] [Module ℂ Vo']
    (πA : Representation ℂ (GL (Fin r) k) VA) (πB : Representation ℂ (GL (Fin t) k) VB)
    {πc : Representation ℂ (GL (Fin 2) k) Vc} {πc' : Representation ℂ (GL (Fin 2) k) Vc'}
    {πi : Representation ℂ (GL (Fin (2 + t)) k) Vi} {πi' : Representation ℂ (GL (Fin (2 + t)) k) Vi'}
    {πo : Representation ℂ (GL (Fin (r + (2 + t))) k) Vo} {πo' : Representation ℂ (GL (Fin (r + (2 + t))) k) Vo'}
    (Ei : (prod₂ πc πB).Equiv πi) (Ei' : (prod₂ πc' πB).Equiv πi') (Eo : (prod₂ πA πi).Equiv πo)
    (Eo' : (prod₂ πA πi').Equiv πo') (T : πc.IntertwiningMap πc') (hT : KInj k T) :
    ∃ T' : πo.IntertwiningMap πo', KInj k T' := by
  let M : πi.IntertwiningMap πi' :=
    Ei'.toIntertwiningMap.comp ((GlobalTheory.CompanionTheory.CuspStd.prod₂MapL T πB).comp Ei.symm.toIntertwiningMap)
  have hM : KInj k M :=
    kinj_comp _ _ (kinj_comp _ _ (kinj_equiv _) (kinj_prod₂MapL T hT _)) (kinj_equiv _)
  exact ⟨Eo'.toIntertwiningMap.comp ((GlobalTheory.CompanionTheory.CuspStd.prod₂MapR πA M).comp Eo.symm.toIntertwiningMap),
    kinj_comp _ _ (kinj_comp _ _ (kinj_equiv _) (kinj_prod₂MapR _ M hM)) (kinj_equiv _)⟩

end PositivityTheory.Rg.BcB.N3.PseStage

end
