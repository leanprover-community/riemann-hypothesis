import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.NakayamaChar
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace GlobalTheory.SingleDatum.MovedLevel

theorem cSep_mem {D : D7} {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) :
    cSep l ∈ Mfr l ∧ cSep l - 1 ∈ l.Mb := by
  have hex : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    have : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l := by rw [show l.Mb ⊔ Mfr l = ⊤ from l.coprime]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 this
    exact ⟨y, hy, by rw [← hxy, sub_add_cancel_right]; exact neg_mem hx⟩
  unfold cSep; rw [dif_pos hex]; exact hex.choose_spec

theorem finVec_div {D : D7} (W : HSp D) (v : Fin W.rank → D.host.E) (c : D.host.E) :
    finVec W (fun x => v x / c) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] c⁻¹) • finVec W v := by
  funext i
  change (1 : Af D.host.F) ⊗ₜ[D.host.F] (v i / c) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] c⁻¹) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] v i)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, div_eq_inv_mul]

theorem finVec_sub {D : D7} (W : HSp D) (v v' : Fin W.rank → D.host.E) :
    finVec W (v - v') = finVec W v - finVec W v' :=
  funext fun i => TensorProduct.tmul_sub _ _ _


theorem inv_smul_nsmul {D : D7} (W : HSp D) (n : ℕ) (hn : (n : D.host.E) ≠ 0)
    (x : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (n : D.host.E)⁻¹) • (n • x) = x := by
  rw [← Nat.cast_smul_eq_nsmul (Af D.host.F ⊗[D.host.F] D.host.E), smul_smul,
    ← map_natCast (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E) n,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hn,
    ← Algebra.TensorProduct.one_def, one_smul]


end GlobalTheory.SingleDatum.MovedLevel
