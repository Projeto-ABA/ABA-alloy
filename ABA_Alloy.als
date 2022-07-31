module ABA

//---------------SIGNATURES---------------

one sig Professor {
	meusAlunos: set Aluno,
	minhasTurmas: set Turma
}

sig Turma {
	alunos: set  Aluno
}


sig PlanoDesenvolvimento {
	atividades: set Atividade,
}


sig Aluno {
	planosDesenvolvimento: set PlanoDesenvolvimento
}

sig Atividade {}

---------------PRED---------------
-- Aluno em Professor
pred alunoEmProfessor[a: Aluno, p: Professor] {
    a in p.meusAlunos
}

-- Aluno em Turma
pred alunoEmTurma[a: Aluno, t: Turma] {
    a in t.alunos
}

-- Turma em Professor
pred turmaEmProfessor[t: Turma, p: Professor] {
    t in p.minhasTurmas
}

-- Plano de desenvolvimento em Aluno
pred planoEmAluno[pd: PlanoDesenvolvimento, a: Aluno] {
    pd in a.planosDesenvolvimento
}

-- A arividade pertence a um plano de desenvolvimento
pred atividadeEmPlanoDsenvolvimento[at: Atividade, pd: PlanoDesenvolvimento] {
    at in pd.atividades
}

---------------FACTS---------------

-- Toda aluno tem Professor
fact alunoPertencemAProfessor {
	all a: Aluno | one p: Professor |  alunoEmProfessor[a, p]
}

-- Alguns alunos pertencem a uma turma
fact alunosPertencemATurma {
	some a: Aluno | one t: Turma | alunoEmTurma[a, t]
}

-- Toda turma tem pelo menos um aluno
fact todaTurmaTemAluno{
	all t: Turma | some a: Aluno | alunoEmTurma[a, t]
}

-- Toda turma pertence a um professor 
fact turmaPertencemAProfessor {
	all t: Turma | one p: Professor | turmaEmProfessor[t, p]
}

-- Alunos podem pertencer a apenas uma turma
fact alunosPertencemAApenasUmaTurma {
	all a: Aluno | lone t: Turma | alunoEmTurma[a, t]
}

-- Todo aluno pode ter mais de um plano de desenvolvimento
fact planoDesenvolvimentoPertenceAAluno {
	all a: Aluno | some pd: PlanoDesenvolvimento | planoEmAluno[pd, a]
}

-- Todo plano de desenvolvimento tem um aluno
fact planoDesenvolvimentoPertenceAAluno {
	all pd: PlanoDesenvolvimento | one a: Aluno | planoEmAluno[pd, a]
}

-- Toda atividade pertence a um plano de desenvolvimento
fact atividadePertenceAPlanoDesenvolvimento {
	all at: Atividade | one pd: PlanoDesenvolvimento | atividadeEmPlanoDsenvolvimento[at, pd]
}

-- Todo plano de desenvolvimento tem pelo menos uma atividade
fact planoTemAtividades {
	all pd: PlanoDesenvolvimento | some at: Atividade | atividadeEmPlanoDsenvolvimento[at, pd]
}

pred show[]{
	#Turma = 3
	#Aluno = 5
}


run show for 15