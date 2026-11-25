module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.DetOnto

theorem sigR_sigR (D : D7) (a : Af D.host.F ⊗[D.host.F] D.host.E) :
    sigR (Af D.host.F) D.sp.cm.sig (sigR (Af D.host.F) D.sp.cm.sig a) = a := by
  induction a using TensorProduct.inductionOn with
  | tmul a b => exact congrArg (fun x => a ⊗ₜ[D.host.F] x) (star_star b)
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem norm_one {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) {a b : R} (h : a * b = 1) :
    a * σ b * σ (a * σ b) = 1 := by
  have h' := congrArg σ h
  rw [map_mul, map_one] at h'
  rw [map_mul, hσ]
  linear_combination (σ a * σ b) * h + h'

theorem infPart_det {D : D7} (V : HSp D) (k : GA D V) (hk : k ∈ GfC V) : infPart D (matHom V k).1.det = 1 := by
  have h : infHom V k = 1 := hk
  have h' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  rw [← h', h, Units.val_one, Matrix.det_one]

theorem infPart_sigR (D : D7) (x : AE D) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) :=
  GlobalTheory.DetRootCong.map_sigR _ _ x

end GlobalTheory.DetOnto
