module wywus

sig Usuario {
	compra: set ListaDeCompras,
	participa: set Grupo
}

sig ListaDeCompras {
	produtos: some Produto,
	alimenta: one Sistema
}

sig Grupo {
	administradoPor: one Usuario
}

sig Mercado{
	vende: some Produto,
}

sig Produto{
	custa: set Preco,
	melhorCusto: one Preco
}

sig Preco{}

sig Sistema{
	encontra: some Preco,
	gera: set RelatorioDeCompra
}

sig RelatorioDeCompra{}


--Lista de compra é única pra cada usuário
pred listaUnicaPorUsuario{
	all l:ListaDeCompras | #l.~compra = 1
}

--Garantia de que existem usuários no modelo
pred existeUsuario {
	some Usuario
}

--Garantia de que todos os podutos estão ligados a algum mercado
pred ProdutoLigadoMercado{
	all p:Produto | some p.~vende
}

-- Garantia de que se um usuário administra um grupo, então ele também participa desse grupo
pred seAdministraParticipa{
	all u:Usuario, b:Grupo |  b.administradoPor = u => u.participa in  b
}

--Todos os modelos devem possuir um e somente um sistema
pred existeUmSistema{
	one Sistema
}

--Garantia de que todo preco pertence a somente um produto
pred PrecoPossuiMelhorPrecoPertenceSoUmProduto {
	all p:Preco |  (#p.~custa = 1 && #p.~melhorCusto = 0) || (#p.~custa = 0 && #p.~melhorCusto = 1)
}

--Garantia de que todos os produtos teram precos
pred ExistemMaisPrecosQueProdutos{
	#Preco > #Produto
}

--O sistema é responsável por encontrar o melhor preço de cada produto
pred SistemaEncontraMelhorPreco{
	#Sistema.encontra = #Produto
	all p:Sistema.encontra | #p.~melhorCusto = 1
}

--O sistema gera relatórios de compras
pred SistemaGeraRelatorioDeCompras{
	#Sistema.gera = #ListaDeCompras
}

--O sistema gera N relatorio de compras, logo a quantidade de relatorio de compras deve ser igual a N
pred qtdDeRelatorioDeCompras{
	#Sistema.gera = #RelatorioDeCompra
}

--A quantidade De Preços deve ser igual a quantidade de Mercados existentes que vendem aquele produto
pred qtdPrecos{
	all p:Produto | #p.custa + #p.melhorCusto = #p.~vende
}


fact{
	PrecoPossuiMelhorPrecoPertenceSoUmProduto
	existeUsuario
	ProdutoLigadoMercado
	seAdministraParticipa
	existeUmSistema
	SistemaEncontraMelhorPreco
	ExistemMaisPrecosQueProdutos
	listaUnicaPorUsuario
	SistemaGeraRelatorioDeCompras
	qtdPrecos
	qtdDeRelatorioDeCompras
}

assert supermercadoOferecerProdutoImplicaEmProdutoTerPreco{
	all p:Produto | #p.~vende >= #p.custa + #p.melhorCusto 
}



pred show[] {}
run show for 25
