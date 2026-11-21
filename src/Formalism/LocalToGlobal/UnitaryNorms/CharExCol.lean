import Formalism.LocalToGlobal.UnitaryNorms.CharExEta
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharExtend
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdeleUnitsOpen

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

def AlgValsFin (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ (χ : HChar L) (s : ℝ) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) * ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∃ C : Subfield ℂ, FiniteDimensional ℚ C ∧ χ.ValuesIn s C.subtype

open Formalism.L2.Col

variable {X : Fields} (σ₀ : X.K →+* ℂ)

structure EtaTQc (Φ : Ideles X.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  unitU : ∀ u ∈ unitIdeles X.E, ‖((Φ u : ℂˣ) : ℂ)‖ = 1
  unr : ∀ v x, IsUnitAt v x → Φ (localIdele X.E v x) = 1
  resFin : ∀ v k, Φ (aF X.F v k) = etaFin (L := X.E) X.F v k
  resInf : ∀ w k, Φ (aFi X.F w k) = etaInf X.F w k
  inf : ∀ k : X.Eˣ, ((Φ (infDiag k) : ℂˣ) : ℂ) =
    ∏ τ, (X.embC σ₀ τ (k : X.E) / ((‖X.embC σ₀ τ (k : X.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)
  glob : ∀ k : X.Eˣ, diagUnits X.E k ∈ unitF (L := X.E) X.F → Φ (diagUnits X.E k) = 1


structure MuZeroQuasiCharacterCondition {Pr : Primes X} {m : ℕ} (Ch : Chars X Pr m) (e : X.Tau → ℚ) (j : Fin m) (Φ : Ideles X.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  unitU : ∀ u ∈ unitIdeles X.E, ‖((Φ u : ℂˣ) : ℂ)‖ = 1
  trivFin : ∀ v k, Φ (aF X.F v k) = 1
  trivInf : ∀ w k, Φ (aFi X.F w k) = 1
  inf : ∃ n : X.Tau → ℤ, (∀ τ, (n τ : ℚ) = 2 * (-e τ)) ∧ ∀ k : X.Eˣ, ((Φ (infDiag k) : ℂˣ) : ℂ) =
    ∏ τ, (X.embC σ₀ τ (k : X.E) / ((‖X.embC σ₀ τ (k : X.E)‖ : ℝ) : ℂ)) ^ n τ
  unr : ∀ v : HeightOneSpectrum (𝓞 X.E), (∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal) → ∀ x, IsUnitAt v x →
    Φ (localIdele X.E v x) = 1
  tame : ∀ v x, IsUnitAt v x → Valued.v ((x : v.adicCompletion X.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) →
    Φ (localIdele X.E v x) = 1
  atg : ∀ (w : {w // w ∈ Pr.vGs}) (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), (x : X.E) = (y : X.E) →
    (c : 𝓞 X.E ⧸ w.1.asIdeal) = Ideal.Quotient.mk w.1.asIdeal y →
    ((Φ (localIdele X.E w.1 (atFin w.1 x)) : ℂˣ) : ℂ) = σ₀ (((Ch.chi j w c)⁻¹ : X.Kˣ) : X.K)
  glob : ∀ k : X.Eˣ, diagUnits X.E k ∈ unitF (L := X.E) X.F → Φ (diagUnits X.E k) = 1



def cEtaC (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) : ℂˣ :=
  if (aboveF (L := X.E) X.F (P.under (𝓞 X.F))).card = 1 then -1 else 1

def etaValC (k : X.Eˣ) : ℂ :=
  ((unrQ X.E (cEtaC X) (diagUnits X.E k) : ℂˣ) : ℂ) *
    ∏ τ, (X.embC σ₀ τ (k : X.E) / ((‖X.embC σ₀ τ (k : X.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)

def EtaFinCheckC (X : Fields) : Prop := ∀ v k, unrQ X.E (cEtaC X) (aF X.F v k) = etaFin (L := X.E) X.F v k

open Classical in

def EtaInfCheckC : Prop := ∀ (w : InfinitePlace X.F) (k : X.Fˣ),
  (∏ i ∈ Finset.univ.filter (fun i => InfinitePlace.mk (X.embC σ₀ i) ∈ aboveInf (L := X.E) X.F w),
    (X.embC σ₀ i ((upF X.F k : X.Eˣ) : X.E) / ((‖X.embC σ₀ i ((upF X.F k : X.Eˣ) : X.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)) =
    ((etaInf X.F w k : ℂˣ) : ℂ)

def GlobFormC (X : Fields) (s0 : X.E) : Prop := ∀ k : X.Eˣ, diagUnits X.E k ∈ unitF (L := X.E) X.F →
  ∃ a : X.Fˣ, k = upF X.F a ∨ ∃ s : X.Eˣ, (s : X.E) = s0 ∧ k = s * upF X.F a

def EtaRecFC : Prop := ∀ a : X.Fˣ, etaValC σ₀ (upF X.F a) = 1

def EtaSqrtDC (s0 : X.E) : Prop := ∀ s : X.Eˣ, (s : X.E) = s0 → etaValC σ₀ s = 1





end CharEx

end Formalism.L2.Host
