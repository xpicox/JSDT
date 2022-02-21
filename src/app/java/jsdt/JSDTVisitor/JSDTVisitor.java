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
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
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
import java.util.function.Predicate;
import java.util.regex.MatchResult;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static jsdt.JSDTVisitor.JSDTVisitorUtils.*;

public class JSDTVisitor implements UnitOLVisitor {

	private final List< CompilationUnit > compilationUnits = new LinkedList<>();;
	private final String packageName;
	private Stack< String > lineage = new Stack<>();
	private Stack< Optional< String > > enclosingUnionName = new Stack<>();
	private final Set< TypeDefinition > collectedInterfaceTypes = new HashSet<>();
	private final Map< String, ServiceNode > serviceDeclarations = new HashMap<>();
	private final Map< String, InterfaceDefinition > interfaceDeclarations = new HashMap<>();
	private final Map< String, TypeDefinition > topLevelTypeDeclarations = new HashMap<>();
	private static String UNDEFINED_VALUE = "Value.UNDEFINED_VALUE";

	// Maps each imported symbol to its import statement
	final Map< String, ImportStatement > importedSymbolsMap = new HashMap<>();
	static private final Map< String, CompilationUnit > visitedTypes = new HashMap<>();

	private JSDTVisitor(String packageName, Program p, String serviceName ) {
		if ( serviceName != null ) {
			collectTopLevelDeclarations( p );
		}
		this.packageName = packageName;
	}

	public static List< CompilationUnit > generateJavaServiceInterface( Program p, String serviceName, String packageName ) {
		JSDTVisitor jsdt = new JSDTVisitor( packageName, p, serviceName );
		jsdt.topLevelTypeDeclarations.values().forEach( typeDefinition -> {
			StringJoiner j = new StringJoiner( " " );
			j.add( "Top level type:" )
					.add( typeDefinition.name() )
					.add( typeDefinition.getClass().getSimpleName() );
			System.out.println( j );
		});
		jsdt.serviceDeclarations.get( serviceName ).accept( jsdt );
		return jsdt.compilationUnits;
	}

	private void collectTopLevelDeclarations( Program program ) {
		for( OLSyntaxNode n : program.children() ) {
			if( n instanceof ImportStatement ) {
				ImportStatement is = (ImportStatement) n;
				ImportSymbolTarget[] importedSymbols = is.importSymbolTargets();
				for( ImportSymbolTarget ist : importedSymbols ) {
					importedSymbolsMap.put( ist.localSymbolName(), is );
				}
			} else if ( n instanceof TypeDefinition ) {
				TypeDefinition td = (TypeDefinition) n;
				topLevelTypeDeclarations.put( td.name(), td);
			} else if ( n instanceof ServiceNode ) {
				ServiceNode s = (ServiceNode) n;
				serviceDeclarations.put( s.name(), s );
			} else if ( n instanceof InterfaceDefinition ) {
				InterfaceDefinition id = (InterfaceDefinition) n;
				interfaceDeclarations.put( id.name(), id );
			}
		}
	}

	public static List< CompilationUnit > generateTypeClasses( TypeDefinition ctx, String packageName ) {
		JSDTVisitor jsdt = new JSDTVisitor( packageName, null, null );
		jsdt.pushName( ctx.name() );
		ctx.accept( jsdt );
		jsdt.popName();
		return jsdt.compilationUnits;
	}

	public static List< CompilationUnit > generateInterfaceClass(InterfaceDefinition ctx, Program program, String packageName) {
		JSDTVisitor jsdt = new JSDTVisitor( packageName, program, null );
		jsdt.visit( ctx );
		return jsdt.compilationUnits;
	}

	public static List< CompilationUnit > generateInterfaceAndTypeClasses(InterfaceDefinition ctx, Program program, String packageName) {
		JSDTVisitor jsdt = new JSDTVisitor(packageName, program, null);
		jsdt.visit(ctx);
		jsdt.collectedInterfaceTypes.forEach(td -> {
			jsdt.compilationUnits.addAll( generateTypeClasses( td, packageName ) );
		});
		return jsdt.compilationUnits;
	}

	static private String normalizeName( String typeOrLabel ) {
		StringBuilder cammelCase = new StringBuilder(typeOrLabel);
		cammelCase.replace(0,1, typeOrLabel.substring(0,1).toUpperCase(Locale.ROOT) );
		Pattern.compile("_+")
				.matcher( typeOrLabel )
				.results()
				// Process matches backwards, otherwise we screw up indexes
				.sorted( Comparator.comparing( MatchResult::start ) )
				// Discard match if it is the last character
				.dropWhile( matchResult -> matchResult.end() >= typeOrLabel.length() )
				.forEach( matchResult -> {
					String charAfterUnderscore = typeOrLabel
							.substring( matchResult.end(), matchResult.end()+1 );
					String upperCaseChar = charAfterUnderscore
							.toUpperCase(Locale.ROOT);
					/* TODO: Use this mangling to get an injective transformation:
					String replacementString = "U".repeat( matchResult.end() - matchResult.start() ) // replace _ for U
							+ ( charAfterUnderscore.equals(upperCaseChar) ? "U" : "" ) // add a U if char was uppercase
							+ upperCaseChar;
					 */
					// Delete dash and uppercase next char
					cammelCase.replace(matchResult.start(), matchResult.end()+1, upperCaseChar);
				} );
		return cammelCase.toString();
	}

	private void pushName( String typeOrLabel ) {
		pushName( typeOrLabel, Optional.empty() );
	}

	private void pushName( String typeOrLabel, String unionName ) {
		 pushName( typeOrLabel, Optional.ofNullable( unionName ) );
	}

	private void pushName( String typeOrLabel, Optional<String> unionName ){
		lineage.push( normalizeName(typeOrLabel) );
		this.enclosingUnionName.push( unionName );
	}

	private String popName() {
		enclosingUnionName.pop();
		return lineage.pop();
	}

	private String getLineage() {
		return String.join( "", lineage );
	}

	private String getParentLineage() {
		return String.join( "", lineage.subList(0, lineage.size() - 1 ) );
	}

	private boolean isUnionCase() {
		return getPeekUnionName().isPresent();
	}

	private Optional< String > getPeekUnionName() {
		return enclosingUnionName.isEmpty() ? Optional.empty() : enclosingUnionName.peek();
	}

	private boolean isTopLevelTypeDeclaration() {
		return lineage.size() == 1;
	}

	private void runInNewLineageContext( Runnable runnable ){
		final Stack< String > lineage = this.lineage;
		final Stack< Optional< String > > enclosingUnionName = this.enclosingUnionName;
		this.lineage = new Stack<>();
		this.enclosingUnionName = new Stack<>();
		runnable.run();
		this.lineage = lineage;
		this.enclosingUnionName = enclosingUnionName;
	}


	/* public void visit( TypeDefinition typeDefinition ) {
		if ( typeDefinition instanceof TypeInlineDefinition ) {
			visit( ( TypeInlineDefinition ) typeDefinition );
		} else if ( typeDefinition instanceof TypeDefinitionLink ) {
			visit( ( TypeDefinitionLink ) typeDefinition );
		} else if ( typeDefinition instanceof TypeChoiceDefinition ) {
			visit( ( TypeChoiceDefinition ) typeDefinition );
		} else {
			throw new RuntimeException( "Unrecognized " + typeDefinition.getClass() );
		}
	} */

	@Override
	public void visit( TypeInlineDefinition typeInlineDefinition ) {
		// TODO: make constructor private
		// TODO: make deafault contructor public
		// TODO: put fields at top of class definition, maybe sort the body of the class
		System.out.println( "Type Inline Definition: " + typeInlineDefinition.name() );

		if ( (isTopLevelTypeDeclaration() && visitedTypes.containsKey( typeInlineDefinition.name() ) ) ||
				typeInlineDefinition.name().equals( "undefined" ) ) {
				return;
		}
		BasicTypeDefinition basicTypeDefinition = typeInlineDefinition.basicType();
		Set< Map.Entry< String, TypeDefinition > > subNodes = typeInlineDefinition.subTypes();

		CompilationUnit compilationUnit = new CompilationUnit();
		compilationUnit.setPackageDeclaration( packageName );

		compilationUnit.addImport( "jolie.runtime.Value" );

		String javaNativeType = jolieToJavaType( basicTypeDefinition.nativeType() );
		if ( javaNativeType.equals( "ByteArray" ) ) {
			compilationUnit.addImport( "jolie.runtime.ByteArray" );
		}

		String className = getLineage();

		ClassOrInterfaceDeclaration theClass = compilationUnit
						.addClass( className, Modifier.Keyword.PUBLIC );

		getPeekUnionName()
				.ifPresent( unionTypeName -> addUnionTypeInterfaceImplementation( theClass, unionTypeName ) );

		/*	Each generated class is composed by:
			- some fields
			- constructor
			- parse method
			- toValue method
		 */
		// Constructor
		ConstructorDeclaration constructorDeclaration = theClass.addConstructor( Modifier.Keyword.PUBLIC );
		BlockStmt constructorDeclarationBody = constructorDeclaration.createBody();
		if ( !basicTypeDefinition.nativeType().equals( NativeType.VOID ) ) {

		}


		// toValue
		MethodDeclaration toValueMethod = theClass.addMethod( "toValue", Modifier.Keyword.PUBLIC );
		BlockStmt toValueMethodBody = toValueMethod.createBody();
		toValueMethodBody.addStatement( "Value value = Value.create();" );
		if ( !basicTypeDefinition.nativeType().equals( NativeType.VOID ) ) {
			toValueMethodBody.addStatement( "value.setValue( root );" );
		}

		// toValueMethodBody.addStatement( "Value value = super.toValue();" );
		toValueMethod.setType( "Value" );

		// parse
		MethodDeclaration parseMethod = theClass.addMethod( "parse", Modifier.Keyword.PUBLIC, Modifier.Keyword.STATIC );
		parseMethod.addParameter( "Value", "value" );

		// TODO: Move logically
		StringJoiner parseReturnParameters = new StringJoiner( ", " );
		if ( !basicTypeDefinition.nativeType().equals( NativeType.VOID ) ) {
			parseReturnParameters.add(
					jolieToGetValueOptional( basicTypeDefinition.nativeType() ).isEmpty() ? "value" : "value." + jolieToGetValueOptional( basicTypeDefinition.nativeType() ).get() + "()" );
		}

		parseMethod.setType( new ClassOrInterfaceType().setName( className ) );
		BlockStmt parseBody = parseMethod.createBody();
		IfStmt parseIfStm = new IfStmt();
		parseBody.addStatement( parseIfStm );
		parseIfStm.setCondition( new ExpressionStmt()
				.setExpression( "value != null"
						+ ( jolieToIsValue( basicTypeDefinition.nativeType() ).isEmpty() ? "" : " && value." + jolieToIsValue( basicTypeDefinition.nativeType() ).get() + "()" ) )
				.getExpression() );
		parseIfStm.setElseStmt( new BlockStmt().addStatement( "return null;" ) );
		BlockStmt ifBranch = new BlockStmt();
		parseIfStm.setThenStmt( ifBranch );

		if ( !basicTypeDefinition.nativeType().equals( NativeType.VOID ) ) {
			constructorDeclaration.addParameter( javaNativeType, "root" );
			FieldDeclaration field = theClass.addField(
					javaNativeType,
					"root",
					Modifier.Keyword.PRIVATE, Modifier.Keyword.FINAL
			);
			field.createGetter().setName( "root" );
			constructorDeclarationBody.addStatement( "this.root = root;" );
		}
		if ( subNodes != null && !subNodes.isEmpty() ) {

			subNodes.forEach( nodeEntry -> {
				String nodeName = nodeEntry.getKey();
				TypeDefinition node = nodeEntry.getValue();
				pushName( nodeName );

				node.accept( this );

				Cardinalities cardinalityClass = getCardinalityClass( node.cardinality() );
				// compilationUnit.addImport( "jsdt.core.cardinality." + cardinalityClass );
				if ( cardinalityClass.equals( Cardinalities.Multi ) ) {
					compilationUnit.addImport( "java.util.stream.Collectors" );
					compilationUnit.addImport( "java.util.List");
					compilationUnit.addImport( "java.util.Optional" );
				} else if (cardinalityClass.equals( Cardinalities.MaybeSingle ) ) {
					compilationUnit.addImport( "java.util.Optional" );
				}

				// TODO: Follow links
				String fieldTypeName = node instanceof TypeDefinitionLink ? ( ( TypeDefinitionLink ) node ).linkedTypeName() : getLineage();
				switch ( fieldTypeName ) {
					case "undefined":
					case "any":
						fieldTypeName = "Value";
				}
				fieldTypeName = normalizeName(fieldTypeName);
				String decoratedFieldTypeName = null;
				switch ( cardinalityClass ) {
					case Single:
						decoratedFieldTypeName = fieldTypeName;
						break;
					case MaybeSingle:
						decoratedFieldTypeName = "Optional<" + fieldTypeName +">";
						break;
					case Multi:
						decoratedFieldTypeName = fieldTypeName.equals("Value") ? fieldTypeName : "Optional<" + fieldTypeName + ">";
						decoratedFieldTypeName = "List<" + decoratedFieldTypeName + ">";
						break;
				}
				FieldDeclaration field = theClass.addField(
						decoratedFieldTypeName,
						nodeName,
						Modifier.Keyword.PRIVATE, Modifier.Keyword.FINAL
				);
				constructorDeclaration.addParameter( decoratedFieldTypeName, nodeName );
				constructorDeclarationBody.addStatement( "this." + nodeName + "=" + nodeName + ";" );
				field.createGetter().setName( nodeName );
				// TODO: go on from here
				StringJoiner s = new StringJoiner( " " );
				if ( cardinalityClass.equals( Cardinalities.Multi ) ) {
					s // .add( cardinalityClass + "<" + fieldTypeName + ">" )
							.add( decoratedFieldTypeName )
							.add( nodeName )
							.add( "=" )
							.add( "value.getChildren(" )
							.add( "\"" + nodeName + "\"" );
					if ( !fieldTypeName.equals( "Value" ) ) {
						s.add( ").stream().map(" )
								.add( fieldTypeName + "::parse ).map(" )
								.add( "Optional::ofNullable" )
								.add( ").collect( Collectors.toList() );" );
					} else {
						s.add( ").values();" );
					}
				} else {
					String childGetter = "value.getFirstChild( \"" + nodeName + "\" )";
					s.add( decoratedFieldTypeName )
							.add( nodeName )
							.add( "=" );
					if ( cardinalityClass.equals( Cardinalities.MaybeSingle ) ) {
						StringJoiner condition = new StringJoiner( " " );
						condition.add( "value.getChildren().isEmpty ?")
								.add( "Optional.empty() :"  )
								.add( "Optional.of(" );
						if ( !fieldTypeName.equals( "Value" ) ) {
							condition.add(fieldTypeName + ".parse(")
									.add(childGetter)
									.add(") );");
						} else {
							condition.add(childGetter).add( ");");
						}
						s.add( condition.toString());
					} else {
						if ( fieldTypeName.equals( "Value" ) ) {
							s.add( childGetter + ";" );
						} else {
							s.add( fieldTypeName + ".parse(" )
									.add( childGetter )
									.add( ");" );
						}
					}
				}
				// System.out.println( s.toString() );
				ifBranch.addStatement( s.toString() );
				parseReturnParameters.add( nodeName );
				// TODO: correctly generate toValue code
				// toValueMethodBody.addStatement( "this." + nodeName + "().addChildenIfNotEmpty(\"" + nodeName + "\", value);" );
				popName();
			} );
		}
		ifBranch.addStatement( "return new " + getLineage() + "(" + parseReturnParameters + ");" );
		toValueMethodBody.addStatement( "return value;" );

		compilationUnits.add( compilationUnit );

		if ( isTopLevelTypeDeclaration() && !isUnionCase() ) {
			visitedTypes.put( typeInlineDefinition.name(), compilationUnit );
		}
	}

	/* We are going to implement idea 1.
	   Example and rationale behind top level type definiontion links.

	   Problem 1:
	   Jolie: type A : B
       Conflicting requirements if translated to Java because we don't have newtypes or type synonyms:
       1. Wherever I expect an A, I have to provide a B: A is a superclass of B. Or I must be able to convert B to A.
       2. A must have same fields and methods of B: A should be a subclass of B? No code duplication if A extends B.
          Also B does not need to know about A. Undesired effect: I can use A to initialize B, but it's still sound.
	   Some Solutions:
       To mitigate point 1: Allocation happens only though default constructor.
       To mitigate point 2: Fields can be set to private.
       Problem with mitigation 1: how to default initialize a field which corresponds to an interface?
       If B gets translated to an interface, we have only case 1, i.e., we want to be able to initialize A
       with subtypes of the interface B. So A must implement the empty interface B.

       Problem 2:
       type A : B
       type C : B
       No multiple inheritance in java, so A and C can not be classes if considering some subtyping solution.

	   More robust ideas:
       1. Follow typelinks to ignore them completely. We are going through this idea for the time being.
       2. Generate class A, generate class B, generate cast methods between the two independent classes.
       3. Generate two types from a Jolie type: a parsing type and a serializing type with different hierarchies.
    */
	@Override
	public void
	visit( TypeDefinitionLink typeDefinitionLink ) {
		// TODO: Properly generate typelinks, also for union cases
		System.out.println( "Type Link Definition: " + typeDefinitionLink.name() + " " + typeDefinitionLink.linkedTypeName() );
		if ( isTopLevelTypeDeclaration() && visitedTypes.containsKey( typeDefinitionLink.name() ) ) {
			// In case this typeLink has already been generated, we must extend it with
			// the implementation of the union type we are dealing with right now (if any)
			// Need if the same type is being used in several unions
			getPeekUnionName().ifPresent( enclosingUnionName -> visitedTypes
					.get( typeDefinitionLink.name() )
					// This is fine because it's a top level type definition
					.getClassByName( normalizeName( typeDefinitionLink.name() ) )
					.ifPresent( theClass ->
							// TODO: Handle case of theClass being an interface
							addUnionTypeInterfaceImplementation( theClass, enclosingUnionName )
					) );
			return;
		}

		// TODO: Generate implementation of interface if link to a union type
		// TODO: Generate protected copy constructor from super class. Todo: What if super class is an interface???
		// TODO: Correctly generate parse method
		if ( isTopLevelTypeDeclaration() ) {
			final String classOrInterfaceName = getLineage();
			final String linkedTypeName = normalizeName(typeDefinitionLink.linkedTypeName());
			final CompilationUnit compilationUnit = new CompilationUnit();
			compilationUnit.setPackageDeclaration(packageName);
			compilationUnit.addImport("jolie.runtime.Value");
			// Extend either the class or the interface of the linked type
			ClassOrInterfaceDeclaration classOrInterfaceDeclaration = compilationUnit
					.addClass(classOrInterfaceName)
					.addExtendedType(linkedTypeName)
					.setInterface(typeDefinitionLink.linkedType() instanceof TypeChoiceDefinition);
			classOrInterfaceDeclaration
					.addMethod("parse", Modifier.Keyword.STATIC, Modifier.Keyword.PUBLIC )
					.setType( classOrInterfaceName )
					.addParameter("Value", "value")
					.createBody();
			compilationUnits.add( compilationUnit );
			if ( !isUnionCase() ) {
				visitedTypes.put( typeDefinitionLink.name(), compilationUnit );
			}
		}

		final Optional<String> unionName = getPeekUnionName();
		runInNewLineageContext( () -> {
			pushName( typeDefinitionLink.linkedTypeName(), unionName );
			typeDefinitionLink.linkedType().accept( this );
			popName(); // not needed beacuse context will be discarded anyway
		} );
	}

	private static TypeDefinition followTypeDefinitionLinks( TypeDefinitionLink typeDefinitionLink ) {
		while ( typeDefinitionLink.linkedType() instanceof TypeDefinitionLink ) {
			typeDefinitionLink = (TypeDefinitionLink) typeDefinitionLink.linkedType();
		}
		return typeDefinitionLink.linkedType();
	}

	private static TypeDefinition followTypeDefinitionLinks( TypeDefinition t ) {
		return t instanceof TypeDefinitionLink ? followTypeDefinitionLinks( (TypeDefinitionLink) t ) : t;
	}

	/*
	- Union types should not be classes because there is no multiple inheritance in java
    - We want a way to default initialize UnionTypes!
    - And then to change easily the field type if we want to change the default value
    How union types get translated:
    Jolie code
	type U : A | B | C
	becomes:
    public interface U {
        // Pattern matching with a visitor
        <R> R when(Is<? extends R> c); // Switch
       	interface Is<R> {              // Cases
        	R is(A v);
        	R is(B v);
        	R is(C v);
    	}

    	// Jolie Value interface
    	Value toValue();
    	static U parse( Value v ) { ... }

    	// Optional-like interface
    	<R> Optional<? extends R> map(As<? extends R> cases);
    	interface As<R> {
     		R as(A v);
        	R as(B v);
        	R as(C v);
    	}
    	default U empty() {
        	return EMPTY;
    	}

    	U EMPTY = new U() { // Optional Empty
        	@Override
        	public <R> R when(Is<? extends R> c) {
            	throw new NoSuchElementException( "No value present" );
        	}

        	@Override
        	public <R> Optional<? extends R> ifPresent(As<? extends R> cases) {
            	return Optional.empty();
        	}

        	@Override
        	public Value toValue() {
            	return new NoSuchElementException( "No value present" );
        	}
    	};
    }
    class A implements U { ... }
    class B implements U { ... }
    class C implements U { ... }
     */
	@Override
	public void visit( TypeChoiceDefinition typeChoiceDefinition ) {
		System.out.println( "Type Choice Definition: " + typeChoiceDefinition.name() );
		// TODO: Handle this type-choice being an alternative of an outer one
		if ( isTopLevelTypeDeclaration() && visitedTypes.containsKey( typeChoiceDefinition. name() ) ) {
			return;
		}
		List<TypeDefinition> unionCases = collectTypeChoiceCases( typeChoiceDefinition );

		CompilationUnit compilationUnit = new CompilationUnit();
		compilationUnit.setPackageDeclaration( packageName );
		compilationUnit.addImport( "jolie.runtime.Value" );
		compilationUnit.addImport( "java.util.NoSuchElementException" );
		compilationUnit.addImport( "java.util.Optional" );

		// Declare interface U
		final String interfaceName = getLineage();
		final ClassOrInterfaceDeclaration unionInterface = compilationUnit.addInterface( interfaceName )
				.setModifier( Modifier.Keyword.PUBLIC, true );
		final String visitorInterfaceName = "Is";
		// Declare visitor interface
		ClassOrInterfaceDeclaration visitorInterface =
				new ClassOrInterfaceDeclaration()
						.setInterface( true )
						.setName( visitorInterfaceName )
						.addTypeParameter( "R" );
		unionInterface.addMember( visitorInterface );
		// Declare switch-like method
		final String switchMethodName = "when";
		MethodDeclaration switchMethod = unionInterface
				.addMethod( switchMethodName )
				.addTypeParameter( "R" )
				.setType( "R" )
				.addParameter( interfaceName + "." + visitorInterfaceName + "<? extends R>", "cases" )
				.removeBody();
		// Declare toValue method
		MethodDeclaration toValueMethod = unionInterface
				.addMethod( "toValue" )
				.setType( "Value" )
				.removeBody();
		// Declare parse method
		BlockStmt parseBody = unionInterface
				.addMethod( "parse", Modifier.Keyword.STATIC )
				.setType( interfaceName )
				.addParameter( "Value", "value")
				.createBody();
		parseBody.addStatement( new StringJoiner( " ")
				.add( interfaceName )
				.add( "result = null;")
				.toString() );
		// Setup Optional-like interface

		// map method
		final String mapMethodName = "map";
		MethodDeclaration mapMethod = unionInterface
				.addMethod( mapMethodName )
				.addTypeParameter( "R" )
				.setType( "Optional<? extends R>" )
				.addParameter( interfaceName + "." + visitorInterfaceName + "<? extends R>", "cases" )
				.removeBody();
		// empty method
		final String emptyFieldName = "EMPTY_" + interfaceName.toUpperCase();
		unionInterface
				.addMethod( "empty", Modifier.Keyword.STATIC )
				.setType( interfaceName )
				.setBody( new BlockStmt().addStatement( new ReturnStmt( emptyFieldName ) ) );
		// EMPTY field declaration and initialization
		final ObjectCreationExpr anonymousClassCreation = new ObjectCreationExpr()
				.setType( interfaceName );
		unionInterface.addField( interfaceName, emptyFieldName )
				.getVariable( 0 )
				.setInitializer( anonymousClassCreation );
		final ClassOrInterfaceDeclaration anonymousClassBody = new ClassOrInterfaceDeclaration();
		final ThrowStmt throwNoSuchElement = new ThrowStmt( new ObjectCreationExpr()
				.setType( "NoSuchElementException" )
				.addArgument( "\"No value present\"" ) );
		// AnonymousClass - switch method implementation
		anonymousClassBody
				.addMethod( switchMethod.getNameAsString(), Modifier.Keyword.PUBLIC )
				.addAnnotation( "Override" )
				.addTypeParameter( switchMethod.getTypeParameter( 0 ) )
				.setType( switchMethod.getType() )
				.addParameter( switchMethod.getParameter( 0 ) )
				.setBody( new BlockStmt().addStatement( throwNoSuchElement ) );
		// AnonymousClass - toValue method implementation
		anonymousClassBody
				.addMethod( toValueMethod.getNameAsString(), Modifier.Keyword.PUBLIC )
				.addAnnotation( "Override" )
				.setType( toValueMethod.getType() )
				.setBody( new BlockStmt().addStatement( throwNoSuchElement ) );
		// AnonymousClass - map method implementation
		anonymousClassBody
				.addMethod( mapMethod.getNameAsString(), Modifier.Keyword.PUBLIC )
				.addAnnotation( "Override" )
				.addTypeParameter( mapMethod.getTypeParameter( 0 ) )
				.setType( mapMethod.getType() )
				.addParameter( mapMethod.getParameter( 0 ) )
				.setBody( new BlockStmt().addStatement( new ReturnStmt( "Optional.empty()" ) ) );
		anonymousClassCreation.setAnonymousClassBody( anonymousClassBody.getMembers() );
		// AnonymousClass - End of EMPTY field initialization


		// used in parseBody
		IfStmt returnResultIfNotNull = new IfStmt()
				.setCondition( new ExpressionStmt().setExpression( "result != null" ).getExpression() )
				.setThenStmt( new ReturnStmt("result") );

		int unionCaseNumber = 0;
		Set<String> caseTypeNamesAlreadyPresent = new HashSet<>();
		for ( TypeDefinition t : unionCases ) {
			unionCaseNumber += 1;
			final String resolvedCaseTypeName = followTypeDefinitionLinks(t).name();
			final String fullyQualifiedCaseTypeName;
			final String simpleCaseName;
			// Generate compilation units for this case
			if ( resolvedCaseTypeName.equals( typeChoiceDefinition.name() ) ) {
				// t is an inline definition of this union
				simpleCaseName = "Case" + unionCaseNumber;
				fullyQualifiedCaseTypeName = interfaceName + simpleCaseName;
			} else if ( !caseTypeNamesAlreadyPresent.contains( resolvedCaseTypeName ) ){
				// TODO: What if t was a link to another union
				// t is a TypeDefinitionLink and we never encountered the linked typename yet in this union type
				fullyQualifiedCaseTypeName = simpleCaseName = normalizeName( resolvedCaseTypeName );
				caseTypeNamesAlreadyPresent.add( resolvedCaseTypeName );
			} else {
				// t is a TypeDefinitionLink and we already encountered the linked typename in this union type
				continue;
			}
			visitorInterface
					.addMethod( "is" )
					.setType( "R" )
					.addParameter( fullyQualifiedCaseTypeName, "v" )
					.removeBody();
			/*
			parseBody.addStatement( new AssignExpr()
					.setOperator( AssignExpr.Operator.ASSIGN)
					.setTarget( new NameExpr("result") )
					.setValue( new MethodCallExpr(
							new NameExpr(caseName),
							"parse",
							NodeList.nodeList( new NameExpr("value") ) ) ) );
			 */
			/*
			Generation of parse body which does not handle overlapping unions,
			since it returns the first successful parse.
			 */
			String parseCall = fullyQualifiedCaseTypeName + ".parse( value );";
			if ( unionCaseNumber < unionCases.size() ) {
				parseBody.addStatement( "result = " + parseCall );
				parseBody.addStatement( returnResultIfNotNull );
			} else {
				parseBody.addStatement( "return " + parseCall );
			}

			pushName( simpleCaseName, interfaceName );
			t.accept( this );
			popName();
		}
		compilationUnits.add( compilationUnit );
		if ( isTopLevelTypeDeclaration() ) {
			visitedTypes.put( typeChoiceDefinition.name(), compilationUnit );
		}
	}
	/*
	Collect all alternatives of a TypeChoice, resolving type links while traversing the ast.
	 */
	private List<TypeInlineDefinition> collectResolvedTypeChoiceCases( TypeChoiceDefinition typeChoiceDefinition ) {
		List<TypeInlineDefinition> unionCases = new ArrayList<>();
		TypeChoiceDefinition tdl = typeChoiceDefinition;
		TypeDefinition left = followTypeDefinitionLinks( tdl.left() );
		TypeDefinition right = followTypeDefinitionLinks( tdl.right() );
		if( left instanceof TypeChoiceDefinition ) {
			unionCases.addAll( collectResolvedTypeChoiceCases( (TypeChoiceDefinition) left) );
		} else {
			unionCases.add( (TypeInlineDefinition) left );
		}
		if( right instanceof TypeChoiceDefinition ) {
			unionCases.addAll( collectResolvedTypeChoiceCases( (TypeChoiceDefinition) right) );
		} else {
			unionCases.add( (TypeInlineDefinition) right );
		}
		return unionCases;
	}

	/*
	Collect all alternatives of a TypeChoice.
	This code relies on the current encoding of TypeChoices in the Jolie AST, i.e.,
	TypeChoiceDefinitions (TDC) are like cons cells of lisp, and an AST for the type
	A | B | C will have the following shape:
		       TDC                     TDC
		┌───────┬───────┐       ┌───────┬───────┐
		│   A   │   ◯───┼──────►│   B   │   C   │
		└───────┴───────┘       └───────┴───────┘
	 */
	private List<TypeDefinition> collectTypeChoiceCases( TypeChoiceDefinition tcd ) {
		List<TypeDefinition> unionCases = new ArrayList<>( List.of( tcd.left() ) );
		while ( tcd.right() instanceof TypeChoiceDefinition ) {
			tcd = (TypeChoiceDefinition) tcd.right();
			unionCases.add( tcd.left() );
		}
		unionCases.add( tcd.right() );
		return unionCases;
	}


	private void addUnionTypeInterfaceImplementation( ClassOrInterfaceDeclaration theClass, String interfaceName ) {
		/* Add visitor method:
			@Override
			public <R> R when(UnionType.Cases<R> cases) {
				return cases.is(this);
			}
		 */
		theClass.addImplementedType( interfaceName );
		theClass.addMethod( "when", Modifier.Keyword.PUBLIC )
				.addAnnotation( "Override" )
				.addTypeParameter( "R" )
				.setType( "R" )
				.addParameter( interfaceName + ".Cases<R>", "cases" )
				.setBody( new BlockStmt().addStatement( "return cases.is( this );" ) );
	}


	@Override
	public void visit( InterfaceDefinition interfaceDefinition ) {
		interfaceDefinition.operationsMap().values().forEach( op -> op.accept( this ) );
	}


	@Override
	public void visit(Program n) {

	}

	@Override
	public void visit( OneWayOperationDeclaration decl ) {
		Optional.of( decl.requestType() ).stream()
				.filter( Predicate.not(TypeInlineDefinition.class::isInstance) )
				.findFirst()
				.ifPresent( type -> {
					pushName( type.name() );
					type.accept( this );
					popName();
				} );
	}

	@Override
	public void visit( RequestResponseOperationDeclaration decl ) {
		Optional.of( decl.requestType() )
				.filter( Predicate.not(TypeInlineDefinition.class::isInstance) )
				.ifPresent( type -> {
					pushName( type.name() );
					type.accept( this );
					popName();
				} );
		Optional.of( decl.responseType() )
				.filter( Predicate.not(TypeInlineDefinition.class::isInstance) )
				.ifPresent( type -> {
					pushName( type.name() );
					type.accept( this );
					popName();
				} );
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
		List<InterfaceDefinition> interfaceDefinitions = n.program().children().stream()
				.filter( InputPortInfo.class::isInstance )
				.map( InputPortInfo.class::cast )
				.findAny()
				.map( InputPortInfo::getInterfaceList )
				.orElse( Collections.emptyList() );
		// Generate JavaServiceClass
		CompilationUnit compilationUnit = new CompilationUnit();
		compilationUnit.addImport( "jolie.runtime.JavaService" );
		compilationUnit.addImport( "jolie.runtime.Value" );
		compilationUnit.setPackageDeclaration( packageName );
		ClassOrInterfaceDeclaration theClass = compilationUnit.addClass( n.name() + "Service" );
		theClass.setModifier( Modifier.Keyword.PUBLIC, true );
		theClass.addExtendedType( "JavaService" );
		// Generate java methods corresponding to jolie interface operations
		interfaceDefinitions.forEach( interfaceDefinition -> {
			interfaceDefinition.operationsMap().forEach( ( name, operation ) -> {
				MethodDeclaration methodDeclaration = theClass.addMethod( name );
				// we do not set the type of the method, since, if it is not set, it defaults to void
				methodDeclaration.setModifiers( Modifier.Keyword.PUBLIC );
				methodDeclaration.addParameter( "Value", "value" );
				BlockStmt methodBody = methodDeclaration.createBody();
				TypeDefinition requestType = operation instanceof OneWayOperationDeclaration ?
						( ( OneWayOperationDeclaration ) operation ).requestType()
						: ( ( RequestResponseOperationDeclaration ) operation ).requestType();
				addParseValueStatement( compilationUnit, methodBody, requestType );
				if ( operation instanceof RequestResponseOperationDeclaration ) {
					compilationUnit.addImport( "jolie.runtime.embedding.RequestResponse" );
					methodDeclaration.addAnnotation( "RequestResponse" );
					methodDeclaration.setType( "Value" );
				}
			} );
		} );
		compilationUnits.add( compilationUnit );
		interfaceDefinitions.forEach( this::visit );
	}

	private static void addParseValueStatement( CompilationUnit compilationUnit, BlockStmt methodBody, TypeDefinition type ) {
		Optional<JolieTypeJavaInfo> javaTypeInfo = Optional.of( type )
				.filter( TypeInlineDefinition.class::isInstance )
				.map( TypeInlineDefinition.class::cast )
				.map( TypeInlineDefinition::basicType )
				.map( BasicTypeDefinition::nativeType )
				.map( JSDTVisitorUtils::getJavaInfo );
		final StringJoiner assignment = new StringJoiner( " " );
		if( javaTypeInfo.isEmpty() ) { // User defined type
			String typeName = normalizeName( type.name() );
			String variableName = type.name();
			assignment.add( typeName )
					.add( variableName )
					.add( "=" )
					.add( typeName + ".parse( value );" );
			methodBody.addStatement( assignment.toString() );
		} else if( javaTypeInfo.get().methodGetValue.isPresent() ) { // Jolie type distinct from void, any, undefined
			final String javaType = javaTypeInfo.get().javaType;
			if ( "ByteArray".equals( javaType ) ) {
				compilationUnit.addImport( "jolie.runtime.ByteArray" );
			}
			final String methodGetValue = javaTypeInfo.get().methodGetValue.get();
			assignment.add( javaType )
					.add( methodGetValue )
					.add( "=" )
					.add( "value." +  methodGetValue + "();");
			methodBody.addStatement( assignment.toString() );
		}
	}

	@Override
	public void visit(EmbedServiceNode n) {

	}
}