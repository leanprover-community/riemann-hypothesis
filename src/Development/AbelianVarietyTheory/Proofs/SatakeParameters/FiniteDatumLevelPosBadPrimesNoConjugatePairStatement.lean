module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePair

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.finiteDatum_level_pos_badPrimes_no_conjugate_pair : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => 0 < (t.rd u μ).lev ∧ ∀ Q ∈ ssRec t u μ, conjPrime₂ Q ∉ ssRec t u μ) := by
  first | exact @GlobalTheory.BadPrimes.lev_pos_and_noConj
