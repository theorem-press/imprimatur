import OAI.SetTheory.PartitionPrinciple.Models.Separation
import Imprimatur

/-! Notation for the partition-principle results of the math catalogue
(PLAN M4, done when). Used in external mode by scripts/integration.sh: the
catalogue itself is untouched. -/

open OAI.PartitionPilot.Forcing

latex_notation SetFormula.Realize U φ ρ => r"#U \models #φ" hide ρ := Fin.elim0 prec := 50
latex_notation ¬ SetFormula.Realize U φ ρ => r"#U \not\models #φ" hide ρ := Fin.elim0 prec := 50
latex_notation SetFormula.pairing => r"\mathsf{Pair}"
latex_notation SetFormula.union => r"\mathsf{Union}"
latex_notation SetFormula.powerSet => r"\mathsf{Power}"
latex_notation SetFormula.infinity => r"\mathsf{Inf}"
latex_notation SetFormula.choice => r"\mathsf{AC}"
latex_notation SetFormula.partitionPrinciple => r"\mathsf{PP}"
latex_notation SetFormula.ZFRealization U => r"#U \models \mathsf{ZF}" prec := 50
latex_notation SetFormula.SeparationSchema U => r"#U \models \mathsf{Sep}" prec := 50
latex_notation SetFormula.CollectionSchema U => r"#U \models \mathsf{Coll}" prec := 50
latex_notation TransitiveGround.sets M => r"#M"
latex_notation Set.Countable s => r"#s\ \text{countable}" prec := 50
latex_notation GroundStandardInaccessible M K => r"#K\ \text{inaccessible in}\ #M" prec := 50
latex_notation ZFSet => r"V"
latex_notation @LE.le (Set _) _ a b => r"#a \subseteq #b" prec := 50
