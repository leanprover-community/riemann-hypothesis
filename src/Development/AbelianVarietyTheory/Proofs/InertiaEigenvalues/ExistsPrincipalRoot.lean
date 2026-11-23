module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ExistsBaseRingOfConjugationFixedTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistLeft

theorem exists_principal_root {D : D7} (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ e : D.host.Eˣ, IsDetRoot V γ (Units.map (incA D).toMonoidHom e) := by
  obtain ⟨γ₀, -, h0⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hdet : ((matHom V γ).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det =
      incA D γ₀.1.det := by
    rw [← GlobalTheory.DetRootRows.det_bc, h0]; rfl
  generalize γ₀.1.det = d at hdet
  have hc : ∀ e : D.host.E, cA D (incA D e) = incA D (star e) := fun e => rfl
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  have hn : star d * d = 1 := by
    have := det_conj_mul V γ
    apply GlobalTheory.DetRootRows.inclR_injective (F := D.host.F) (AF D.host.F)
    rw [map_mul, map_one, ← hc, ← hdet]
    exact this
  obtain ⟨e, he0, he⟩ : ∃ e : D.host.E, e ≠ 0 ∧ e = d * star e := by
    by_cases hd : d = -1
    · obtain ⟨a, ha⟩ := GlobalTheory.RecDict.cmData_sig_ne_id D.sp.cm
      refine ⟨a - star a, sub_ne_zero.2 (Ne.symm ha), ?_⟩
      rw [hd, star_sub, star_star]; ring
    · refine ⟨1 + d, fun h => hd (by linear_combination h), ?_⟩
      rw [star_add, star_one]; linear_combination -hn
  refine ⟨Units.mk0 e he0, ?_⟩
  unfold IsDetRoot
  rw [hdet]
  show incA D e = incA D d * cA D (incA D e)
  rw [hc, ← map_mul, ← he]

theorem muVal_left {D : D7} (V : HSp D) (χ : (AE D)ˣ →* Circle)
    (hE : ∀ x : D.host.Eˣ, χ (Units.map (incA D).toMonoidHom x) = 1) (mu : GA D V → ℂ) (hmu : MuVal V χ mu)
    (γ : GA D V) (hγ : γ ∈ GQ V) (h : GA D V) : mu (γ * h) = mu h := by
  obtain ⟨x, hx⟩ := hmu.1 h
  obtain ⟨e, he⟩ := exists_principal_root V γ hγ
  rw [hmu.2 _ _ (detRootMul_holds V γ h _ x he hx), hmu.2 h x hx, map_mul, hE e, one_mul]

theorem twist_left : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E)
    (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) →
    ∀ γ ∈ GQ V, ∀ h : GA D V, dd (γ * h) = dd h := by
  intro D V pd k _ σ δ δc ht dd hdd γ hγ h
  have hE : ∀ x : D.host.Eˣ, δc (Units.map (incA D).toMonoidHom x) = 1 := ht.1.1.2
  rcases hdd with hm | hm
  · exact muVal_left V δc hE dd hm γ hγ h
  · exact muVal_left V δc⁻¹ (fun x => by rw [MonoidHom.inv_apply, hE x, inv_one]) dd hm γ hγ h

end GlobalTheory.TwistLeft
