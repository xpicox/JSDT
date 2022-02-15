/******************************************************************************
 * Copyright (C) 2021 by Saverio Giallorenzo <saverio.giallorenzo@gmail.com>  *
 *                                                                            *
 * This program is free software; you can redistribute it and/or modify       *
 * it under the terms of the GNU Library General Public License as            *
 * published by the Free Software Foundation; either version 2 of the         *
 * License, or (at your option) any later version.                            *
 *                                                                            *
 * This program is distributed in the hope that it will be useful,            *
 * but WITHOUT ANY WARRANTY; without even the implied warranty of             *
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *
 * GNU General Public License for more details.                               *
 *                                                                            *
 * You should have received a copy of the GNU Library General Public          *
 * License along with this program; if not, write to the                      *
 * Free Software Foundation, Inc.,                                            *
 * 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.                  *
 *                                                                            *
 * For details about the authors of this software, see the AUTHORS file.      *
 ******************************************************************************/

package jsdt.JSDTVisitor;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import jolie.lang.NativeType;
import jolie.lang.parse.UnitOLVisitor;
import jolie.lang.parse.ast.*;
import jolie.lang.parse.ast.courier.CourierChoiceStatement;
import jolie.lang.parse.ast.courier.CourierDefinitionNode;
import jolie.lang.parse.ast.courier.NotificationForwardStatement;
import jolie.lang.parse.ast.courier.SolicitResponseForwardStatement;
import jolie.lang.parse.ast.expression.*;
import jolie.lang.parse.ast.types.*;
import jsdt.core.cardinality.Cardinalities;

import java.util.*;

import static jsdt.JSDTVisitor.JSDTVisitorUtils.*;

public class JSDTVisitor implements UnitOLVisitor {

	private final List< CompilationUnit > compilationUnits;
	private final String packageName;
	private final Stack< String > lineage;
	private final Set< TypeDefinition > collectedInterfaceTypes;
	static private final Set< String > visitedTypes = new HashSet<>();

	private JSDTVisitor(String packageName ) {
		this.compilationUnits = new LinkedList<>();
		this.lineage = new Stack<>();
		this.packageName = packageName;
		this.collectedInterfaceTypes = new HashSet<>();
	}

	public static List< CompilationUnit > generateTypeClasses( TypeDefinition ctx, String packageName ) {
		JSDTVisitor jsdt = new JSDTVisitor( packageName );
		jsdt.lineage.push( ctx.name() );
		jsdt.visit( ctx );
		jsdt.lineage.pop();
		return jsdt.compilationUnits;
	}

	public static List< CompilationUnit > generateInterfaceClass( InterfaceDefinition ctx, String packageName ) {
		JSDTVisitor jsdt = new JSDTVisitor( packageName );
		jsdt.visit( ctx );
		return jsdt.compilationUnits;
	}

	public static List< CompilationUnit > generateInterfaceAndTypeClasses( InterfaceDefinition ctx, String packageName ) {
		JSDTVisitor jsdt = new JSDTVisitor( packageName );
		jsdt.visit( ctx );
		jsdt.collectedInterfaceTypes.forEach( td -> {
			jsdt.compilationUnits.addAll( generateTypeClasses( td, packageName ) );
		} );
		return jsdt.compilationUnits;
	}

	private String getLineage() {
		return String.join( "_", lineage );
	}

	public void visit( TypeDefinition typeDefinition ) {
		if ( typeDefinition instanceof TypeInlineDefinition ) {
			visit( ( TypeInlineDefinition ) typeDefinition );
		} else if ( typeDefinition instanceof TypeDefinitionLink ) {
			visit( ( TypeDefinitionLink ) typeDefinition );
		} else if ( typeDefinition instanceof TypeChoiceDefinition ) {
			visit( ( TypeChoiceDefinition ) typeDefinition );
		} else {
			throw new RuntimeException( "Unrecognized " + typeDefinition.getClass() );
		}
	}

	@Override
	public void visit( TypeInlineDefinition typeInlineDefinition ) {
		if ( typeInlineDefinition.name().equals( "undefined" ) ) {
			return;
		}
		visitedTypes.add( typeInlineDefinition.name() );
		BasicTypeDefinition basicTypeDefinition = typeInlineDefinition.basicType();
		Set< Map.Entry< String, TypeDefinition > > subNodes = typeInlineDefinition.subTypes();

		CompilationUnit compilationUnit = new CompilationUnit();
		compilationUnit.setPackageDeclaration( packageName );

		compilationUnit.addImport( "jsdt.core.types.BasicType" );
		compilationUnit.addImport( "jolie.runtime.Value" );

		String javaNativeType = jolieToJavaType( basicTypeDefinition.nativeType() );
		if ( javaNativeType.equals( "ByteArray" ) ) {
			compilationUnit.addImport( "jolie.runtime.ByteArray" );
		}

		ClassOrInterfaceDeclaration theClass = compilationUnit.addClass( getLineage() )
				.setModifier( Modifier.Keyword.PUBLIC, true )
				.addExtendedType( "BasicType<" + javaNativeType + ">" );

		ConstructorDeclaration constructorDeclaration = theClass.addConstructor( Modifier.Keyword.PUBLIC );
		BlockStmt constructorDeclarationBody = constructorDeclaration.createBody();

		MethodDeclaration parseMethod = theClass.addMethod( "parse", Modifier.Keyword.PUBLIC, Modifier.Keyword.STATIC );
		parseMethod.addParameter( "Value", "value" );

		MethodDeclaration toValueMethod = theClass.addMethod( "toValue", Modifier.Keyword.PUBLIC );
		BlockStmt toValueMethodBody = toValueMethod.createBody();
		toValueMethodBody.addStatement( "Value value = super.toValue();" );
		toValueMethod.setType( "Value" );

		StringJoiner parseReturnParameters = new StringJoiner( ", " );
		if ( !basicTypeDefinition.nativeType().equals( NativeType.VOID ) ) {
			parseReturnParameters.add(
					jolieToGetValueOptional( basicTypeDefinition.nativeType() ).isEmpty() ? "value" : "value." + jolieToGetValueOptional( basicTypeDefinition.nativeType() ).get() + "()" );
		}

		parseMethod.setType( new ClassOrInterfaceType().setName( getLineage() ) );
		BlockStmt parseBody = parseMethod.createBody();
		IfStmt parseIfStm = new IfStmt();
		parseBody.addStatement( parseIfStm );
		parseIfStm.setCondition( new ExpressionStmt()
				.setExpression( "value != null"
						+ ( jolieToIsValue( basicTypeDefinition.nativeType() ).isEmpty() ? "" : " && value." + jolieToIsValue( basicTypeDefinition.nativeType() ).get() + "()" ) )
				.getExpression() );
		BlockStmt ifBranch = new BlockStmt();
		parseIfStm.setElseStmt( new BlockStmt().addStatement( "return null;" ) );
		parseIfStm.setThenStmt( ifBranch );

		if ( !basicTypeDefinition.nativeType().equals( NativeType.VOID ) ) {
			constructorDeclaration.addParameter( jolieToJavaType( basicTypeDefinition.nativeType() ), "root" );
			constructorDeclarationBody.addStatement( "super( root );" );
		} else {
			constructorDeclarationBody.addStatement( "super( null );" );
		}
		if ( subNodes != null && !subNodes.isEmpty() ) {

			subNodes.forEach( nodeEntry -> {
				String nodeName = nodeEntry.getKey();
				TypeDefinition node = nodeEntry.getValue();
				lineage.push( nodeName );

				visit( node );

				Cardinalities cardinalityClass = getCardinalityClass( node.cardinality() );
				compilationUnit.addImport( "jsdt.core.cardinality." + cardinalityClass );
				if ( cardinalityClass.equals( Cardinalities.Multi ) ) {
					compilationUnit.addImport( "java.util.stream.Collectors" );
				}
				String fieldTypeName = node instanceof TypeDefinitionLink ? ( ( TypeDefinitionLink ) node ).linkedTypeName() : getLineage();
				switch ( fieldTypeName ) {
					case "undefined":
					case "any":
						fieldTypeName = "Value";
				}
				FieldDeclaration field = theClass.addField(
						cardinalityClass + "<" + fieldTypeName + ">",
						nodeName,
						Modifier.Keyword.PRIVATE, Modifier.Keyword.FINAL
				);
				constructorDeclaration.addParameter( field.getCommonType(), nodeName );
				constructorDeclarationBody.addStatement( "this." + nodeName + "=" + nodeName + ";" );
				field.createGetter().setName( nodeName );
				StringJoiner s = new StringJoiner( " " );
				if ( cardinalityClass.equals( Cardinalities.Multi ) ) {
					s.add( cardinalityClass + "<" + fieldTypeName + ">" )
							.add( nodeName )
							.add( "=" )
							.add( cardinalityClass + ".of( value.getChildren(" )
							.add( "\"" + nodeName + "\"" );
					if ( !fieldTypeName.equals( "Value" ) ) {
						s.add( ").stream().map(" )
								.add( fieldTypeName + "::parse" );
					} else {
						s.add( ").stream(" );
					}
					s.add( ").collect( Collectors.toList() ) );" );
				} else {
					s.add( cardinalityClass + "<" + fieldTypeName + ">" )
							.add( nodeName )
							.add( "=" )
							.add( cardinalityClass + ".of(" );
					if ( fieldTypeName.equals( "Value" ) ) {
						s.add( "value.getChildren(" )
								.add( "\"" + nodeName + "\"" )
								.add( ").get( 0 ) );" );
					} else {
						s.add( fieldTypeName + ".parse(" )
								.add( "value.getChildren(" )
								.add( "\"" + nodeName + "\"" )
								.add( ").get( 0 ) ) );" );
					}
				}
				ifBranch.addStatement( s.toString() );
				parseReturnParameters.add( nodeName );
				toValueMethodBody.addStatement( "this." + nodeName + "().addChildenIfNotEmpty(\"" + nodeName + "\", value);" );
				lineage.pop();
			} );
		}
		ifBranch.addStatement( "return new " + getLineage() + "(" + parseReturnParameters + ");" );
		toValueMethodBody.addStatement( "return value;" );

		compilationUnits.add( compilationUnit );
	}

	@Override
	public void visit( TypeDefinitionLink typeDefinitionLink ) {
		if ( !visitedTypes.contains( typeDefinitionLink.linkedType().name() ) ) {
			visitedTypes.add( typeDefinitionLink.linkedType().name() );
			this.compilationUnits.addAll(
					JSDTVisitor.generateTypeClasses( typeDefinitionLink.linkedType(), packageName )
			);
		}
	}

	@Override
	public void visit( TypeChoiceDefinition typeChoiceDefinition ) {
		visitedTypes.add( typeChoiceDefinition.name() );
		CompilationUnit compilationUnit = new CompilationUnit();
		compilationUnit.setPackageDeclaration( packageName );

		compilationUnit.addImport( "jsdt.core.types.ChoiceType" );
		compilationUnit.addImport( "jolie.runtime.Value" );

		String leftClassName = typeChoiceDefinition.left() instanceof TypeDefinitionLink ?
				( ( TypeDefinitionLink ) typeChoiceDefinition.left() ).linkedType().name()
				: getLineage() + "_1";
		String rightClassName = typeChoiceDefinition.right() instanceof TypeDefinitionLink ?
				( ( TypeDefinitionLink ) typeChoiceDefinition.right() ).linkedType().name()
				: getLineage() + "_2";

		ClassOrInterfaceDeclaration theClass = compilationUnit.addClass( getLineage() )
				.setModifier( Modifier.Keyword.PUBLIC, true )
				.addExtendedType( "ChoiceType<" + leftClassName + ", " + rightClassName + ">" );
		ConstructorDeclaration constructorDeclaration = theClass.addConstructor( Modifier.Keyword.PUBLIC );
		constructorDeclaration.addParameter( leftClassName, "left" );
		constructorDeclaration.addParameter( rightClassName, "right" );
		BlockStmt constructorDeclarationBody = constructorDeclaration.createBody();
		constructorDeclarationBody.addStatement( "super( left, right );" );

		MethodDeclaration parseMethod = theClass.addMethod( "parse", Modifier.Keyword.PUBLIC, Modifier.Keyword.STATIC );
		parseMethod.addParameter( "Value", "value" );
		parseMethod.setType( new ClassOrInterfaceType().setName( getLineage() ) );
		BlockStmt parseBody = parseMethod.createBody();
		parseBody.addStatement( leftClassName + " left = " + leftClassName + ".parse( value );" );
		parseBody.addStatement( rightClassName + " right = " + rightClassName + ".parse( value );" );
		IfStmt parseIfStm = new IfStmt();
		parseBody.addStatement( parseIfStm );
		parseIfStm.setCondition( new ExpressionStmt().setExpression( "left == null && right == null" ).getExpression() );
		parseIfStm.setThenStmt( new BlockStmt().addStatement( "return null;" ) );
		parseIfStm.setElseStmt( new BlockStmt().addStatement( "return new " + getLineage() + "(left, right);" ) );

		lineage.push( "1" );
		visit( typeChoiceDefinition.left() );
		lineage.pop();

		lineage.push( "2" );
		visit( typeChoiceDefinition.right() );
		lineage.pop();

		compilationUnits.add( compilationUnit );
	}


	@Override
	public void visit( InterfaceDefinition interfaceDefinition ) {
		CompilationUnit compilationUnit = new CompilationUnit();
		compilationUnit.addImport( "jolie.runtime.JavaService" );
		compilationUnit.addImport( "jolie.runtime.Value" );
		compilationUnit.setPackageDeclaration( packageName );
		ClassOrInterfaceDeclaration theClass = compilationUnit.addClass( interfaceDefinition.name() + "Service" );
		theClass.setModifier( Modifier.Keyword.PUBLIC, true );
		theClass.addExtendedType( "JavaService" );
		interfaceDefinition.operationsMap().forEach( ( name, operation ) -> {
			MethodDeclaration methodDeclaration = theClass.addMethod( name );
			// we do not set the type of the method, since, if it is not set, it defaults to void
			methodDeclaration.setModifiers( Modifier.Keyword.PUBLIC );
			methodDeclaration.addParameter( "Value", "value" );
			BlockStmt methodBody = methodDeclaration.createBody();
			TypeDefinition requestType = operation instanceof OneWayOperationDeclaration ?
					( ( OneWayOperationDeclaration ) operation ).requestType()
					: ( ( RequestResponseOperationDeclaration ) operation ).requestType();
			switch ( requestType.name() ) {
				case "void":
					break;
				case "bool":
					methodBody.addStatement( "boolean request = value." + jolieToGetValue( requestType.name() ) + "();" );
					break;
				case "int":
					methodBody.addStatement( "int request = value." + jolieToGetValue( requestType.name() ) + "();" );
					break;
				case "double":
					methodBody.addStatement( "double request = value." + jolieToGetValue( requestType.name() ) + "();" );
					break;
				case "long":
					methodBody.addStatement( "long request = value." + jolieToGetValue( requestType.name() ) + "();" );
					break;
				case "string":
					methodBody.addStatement( "String request = value." + jolieToGetValue( requestType.name() ) + "();" );
					break;
				case "raw":
					compilationUnit.addImport( "jolie.runtime.ByteArray" );
					methodBody.addStatement( "ByteArray request = value." + jolieToGetValue( requestType.name() ) + "();" );
					break;
				default:
					switch ( requestType.name() ) {
						case "any":
						case "undefined":
							break;
						default:
							collectedInterfaceTypes.add( requestType );
							methodBody.addStatement( requestType.name() + " request = " + requestType.name() + ".parse( value );" );
					}
			}
			if ( operation instanceof RequestResponseOperationDeclaration ) {
				compilationUnit.addImport( "jolie.runtime.embedding.RequestResponse" );
				methodDeclaration.addAnnotation( "RequestResponse" );
				TypeDefinition responseType = ( ( RequestResponseOperationDeclaration ) operation ).responseType();
				switch ( responseType.name() ) {
					case "void":
					case "bool":
					case "int":
					case "double":
					case "long":
					case "string":
					case "raw":
					case "any":
					case "undefined":
						break;
					default:
						collectedInterfaceTypes.add( responseType );
				}
				methodDeclaration.setType( "Value" );
			}
		} );
		compilationUnits.add( compilationUnit );
	}


	@Override
	public void visit(Program n) {

	}

	@Override
	public void visit(OneWayOperationDeclaration decl) {

	}

	@Override
	public void visit(RequestResponseOperationDeclaration decl) {

	}

	@Override
	public void visit(DefinitionNode n) {

	}

	@Override
	public void visit(ParallelStatement n) {

	}

	@Override
	public void visit(SequenceStatement n) {

	}

	@Override
	public void visit(NDChoiceStatement n) {

	}

	@Override
	public void visit(OneWayOperationStatement n) {

	}

	@Override
	public void visit(RequestResponseOperationStatement n) {

	}

	@Override
	public void visit(NotificationOperationStatement n) {

	}

	@Override
	public void visit(SolicitResponseOperationStatement n) {

	}

	@Override
	public void visit(LinkInStatement n) {

	}

	@Override
	public void visit(LinkOutStatement n) {

	}

	@Override
	public void visit(AssignStatement n) {

	}

	@Override
	public void visit(AddAssignStatement n) {

	}

	@Override
	public void visit(SubtractAssignStatement n) {

	}

	@Override
	public void visit(MultiplyAssignStatement n) {

	}

	@Override
	public void visit(DivideAssignStatement n) {

	}

	@Override
	public void visit(IfStatement n) {

	}

	@Override
	public void visit(DefinitionCallStatement n) {

	}

	@Override
	public void visit(WhileStatement n) {

	}

	@Override
	public void visit(OrConditionNode n) {

	}

	@Override
	public void visit(AndConditionNode n) {

	}

	@Override
	public void visit(NotExpressionNode n) {

	}

	@Override
	public void visit(CompareConditionNode n) {

	}

	@Override
	public void visit(ConstantIntegerExpression n) {

	}

	@Override
	public void visit(ConstantDoubleExpression n) {

	}

	@Override
	public void visit(ConstantBoolExpression n) {

	}

	@Override
	public void visit(ConstantLongExpression n) {

	}

	@Override
	public void visit(ConstantStringExpression n) {

	}

	@Override
	public void visit(ProductExpressionNode n) {

	}

	@Override
	public void visit(SumExpressionNode n) {

	}

	@Override
	public void visit(VariableExpressionNode n) {

	}

	@Override
	public void visit(NullProcessStatement n) {

	}

	@Override
	public void visit(Scope n) {

	}

	@Override
	public void visit(InstallStatement n) {

	}

	@Override
	public void visit(CompensateStatement n) {

	}

	@Override
	public void visit(ThrowStatement n) {

	}

	@Override
	public void visit(ExitStatement n) {

	}

	@Override
	public void visit(ExecutionInfo n) {

	}

	@Override
	public void visit(CorrelationSetInfo n) {

	}

	@Override
	public void visit(InputPortInfo n) {

	}

	@Override
	public void visit(OutputPortInfo n) {

	}

	@Override
	public void visit(PointerStatement n) {

	}

	@Override
	public void visit(DeepCopyStatement n) {

	}

	@Override
	public void visit(RunStatement n) {

	}

	@Override
	public void visit(UndefStatement n) {

	}

	@Override
	public void visit(ValueVectorSizeExpressionNode n) {

	}

	@Override
	public void visit(PreIncrementStatement n) {

	}

	@Override
	public void visit(PostIncrementStatement n) {

	}

	@Override
	public void visit(PreDecrementStatement n) {

	}

	@Override
	public void visit(PostDecrementStatement n) {

	}

	@Override
	public void visit(ForStatement n) {

	}

	@Override
	public void visit(ForEachSubNodeStatement n) {

	}

	@Override
	public void visit(ForEachArrayItemStatement n) {

	}

	@Override
	public void visit(SpawnStatement n) {

	}

	@Override
	public void visit(IsTypeExpressionNode n) {

	}

	@Override
	public void visit(InstanceOfExpressionNode n) {

	}

	@Override
	public void visit(TypeCastExpressionNode n) {

	}

	@Override
	public void visit(SynchronizedStatement n) {

	}

	@Override
	public void visit(CurrentHandlerStatement n) {

	}

	@Override
	public void visit(EmbeddedServiceNode n) {

	}

	@Override
	public void visit(InstallFixedVariableExpressionNode n) {

	}

	@Override
	public void visit(VariablePathNode n) {

	}

	@Override
	public void visit(DocumentationComment n) {

	}

	@Override
	public void visit(FreshValueExpressionNode n) {

	}

	@Override
	public void visit(CourierDefinitionNode n) {

	}

	@Override
	public void visit(CourierChoiceStatement n) {

	}

	@Override
	public void visit(NotificationForwardStatement n) {

	}

	@Override
	public void visit(SolicitResponseForwardStatement n) {

	}

	@Override
	public void visit(InterfaceExtenderDefinition n) {

	}

	@Override
	public void visit(InlineTreeExpressionNode n) {

	}

	@Override
	public void visit(VoidExpressionNode n) {

	}

	@Override
	public void visit(ProvideUntilStatement n) {

	}

	@Override
	public void visit(ImportStatement n) {

	}

	@Override
	public void visit(ServiceNode n) {

	}

	@Override
	public void visit(EmbedServiceNode n) {

	}
}