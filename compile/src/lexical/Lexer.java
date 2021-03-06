package lexical;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStreamWriter;

public class Lexer {
	public static final String key[];
	public static final String symbol[];
	static{
		key=new String[33];
		key[0] = new String("main");
		key[1] = new String("auto");
		key[2] = new String("short");
		key[3] = new String("int");
		key[4] = new String("long");
		key[5] = new String("float");
		key[6] = new String("double");
		key[7] = new String("char");
		key[8] = new String("struct");
		key[9] = new String("union");
		key[10] = new String("enum");
		key[11] = new String("typedef");
		key[12] = new String("const");
		key[13] = new String("unsigned");
		key[14] = new String("signed");
		key[15] = new String("extern");
		key[16] = new String("register");
		key[17] = new String("static");
		key[18] = new String("volatile");
		key[19] = new String("void");
		key[20] = new String("if");
		key[21] = new String("else");
		key[22] = new String("switch");
		key[23] = new String("case");
		key[24] = new String("for");
		key[25] = new String("do");
		key[26] = new String("while");
		key[27] = new String("goto");
		key[28] = new String("continue");
		key[29] = new String("break");
		key[30] = new String("default");
		key[31] = new String("sizeof");
		key[32] = new String("return");
	}
	static{
		symbol=new String[26];
		symbol[0]=new String("=");
		symbol[1]=new String("+");
		symbol[2]=new String("-");
		symbol[3]=new String("*");
		symbol[4]=new String("/");
		symbol[5]=new String("++");
		symbol[6]=new String("--");
		symbol[7]=new String("+=");
		symbol[8]=new String("-=");
		symbol[9]=new String("*=");
		symbol[10]=new String("/=");
		symbol[11]=new String("==");
		symbol[12]=new String("!=");
		symbol[13]=new String(">");
		symbol[14]=new String("<");
		symbol[15]=new String(">=");
		symbol[16]=new String("<=");
		symbol[17]=new String("(");
		symbol[18]=new String(")");
		symbol[19]=new String("[");
		symbol[20]=new String("]");
		symbol[21]=new String("{");
		symbol[22]=new String("}");
		symbol[23]=new String(",");
		symbol[24]=new String(":");
		symbol[25]=new String(";");
	}
	public char ch;//������¶�����Դ�����ַ�
	public String strToken;//��Ź��ɵ��ʵ��ַ���
	public String text="";
	public int pText=0;//����ָʾ��(�����˶��ٸ��ַ�)
	public int line=1;
	public int number=0;
	
	public void read() throws IOException{
		File fin = new File("source.txt");
		FileReader fr = new FileReader(fin);
		BufferedReader br = new BufferedReader(fr);
		String line;
		while((line = br.readLine()) != null){
			text=text+line;
		}
		br.close();
	}
	
	public void analyse(){
		int code;
	    strToken="";
	    this.getChar();//��һ���ַ�
	    this.getBC();//�����ո�
	    if(this.isLetter()){//ʶ���ʶ���͹ؼ���
	    	while(this.isLetter() || this.isDigit() || ch=='_'){
	    		this.concat();
	    		this.getChar();
	    	}
	    	this.retract();
	    	code=this.reserve();
	    	if(code!=-1){//ʶ��������ǹؼ���
	    		this.writeToFile(code, strToken, line);
	    	}else{//ʶ��������Ǳ�ʶ��
	    		this.writeToFile(33, strToken, line);
	    	}
	    }else if(this.isDigit()){//ʶ�����γ����������ͳ���
	    	while(this.isDigit()){
	    		this.concat();
	    		this.getChar();
	    	}
	    	if(ch!='.'){//ʶ�����ͳ���
	    		this.retract();
	    		this.writeToFile(34, strToken, line);
	    	}else if(ch=='.'){//ʶ��ʵ�ͳ���
	    		this.concat();
	    		this.getChar();
	    		while(this.isDigit()){
	    			this.concat();
	    			this.getChar();
	    		}
	    		this.retract();
	    		this.writeToFile(35, strToken, line);
	    	}
	    }else if(ch==34){//ʶ���ַ�������
	    	this.concat();
    		this.getChar();
    		do{
    			this.concat();
	    		this.getChar();
    		}while(ch!=34);
    		this.writeToFile(63, strToken+"\"", line);
	    }else if(ch==39){//ʶ���ַ�char����
	    	this.getChar();
	    	while(ch!=39){
	    		this.concat();
	    		this.getChar();
	    	}
	    	this.writeToFile(36, strToken, line);
	    }else if(ch=='='){//ʶ��=��==
	    	this.concat();
    		this.getChar();
    		if(ch=='='){
    			this.concat();
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    		}else{
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    			this.retract();
    		}
	    }else if(ch=='+'){//ʶ��+��+=��++
	    	this.concat();
    		this.getChar();
    		if(ch=='='){
    			this.concat();
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    		}else if(ch=='+'){
    			this.concat();
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    		}else{
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    			this.retract();
    		}
	    }else if(ch=='-'){//ʶ��-��-=��--
	    	this.concat();
    		this.getChar();
    		if(ch=='='){
    			this.concat();
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    		}else if(ch=='-'){
    			this.concat();
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    		}else{
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    			this.retract();
    		}
	    }else if(ch=='*'){//ʶ��*��*=
	    	this.concat();
    		this.getChar();
    		if(ch=='='){
    			this.concat();
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    		}else{
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    			this.retract();
    		}
	    }else if(ch=='/'){//ʶ��/��/=
	    	this.concat();
    		this.getChar();
    		if(ch=='='){
    			this.concat();
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    		}else{
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    			this.retract();
    		}
	    }else if(ch=='>'){//ʶ��>,>=
	    	this.concat();
    		this.getChar();
    		if(ch=='='){
    			this.concat();
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    		}else{
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    			this.retract();
    		}
	    }else if(ch=='<'){//ʶ��<,<=
	    	this.concat();
    		this.getChar();
    		if(ch=='='){
    			this.concat();
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    		}else{
    			code=this.findSymbol(strToken);
    			this.writeToFile(code, strToken, line);
    			this.retract();
    		}
	    }else if(ch==';'){
	    	this.writeToFile(62, strToken+";", line);
	    }else if(ch=='('){
	    	this.writeToFile(26, strToken+"(", line);
	    }else if(ch==')'){
	    	this.writeToFile(27, strToken+")", line);
	    }else if(ch=='['){
	    	this.writeToFile(56, strToken+"[", line);
	    }else if(ch==']'){
	    	this.writeToFile(57, strToken+"]", line);
	    }else if(ch=='{'){
	    	this.writeToFile(30, strToken+"{", line);
	    }else if(ch=='}'){
	    	this.writeToFile(31, strToken+"}", line);
	    }else if(ch==','){
	    	this.writeToFile(32, strToken+",", line);
	    }else if(ch=='\n'){
	    	line++;
	    }
	}
	
	public void getChar(){
		ch=text.charAt(pText);
		pText++;
	}
	
	public void getBC(){
		while(true){
			if(ch==' '){
				this.getChar();
			}else{
				break;
			}
		}
	}
	
	public boolean isLetter(){
		if((ch>='a'&&ch<='z') ||(ch>='A'&&ch<='Z') || (ch=='&')){
			return true;
		}
		return false;
	}
	
	public boolean isDigit(){
		if(ch>='0'&&ch<='9'){
			return true;
		}
		return false;
	}
	
	public void concat(){
		strToken+=ch;
	}
	
	public void retract(){
		ch=' ';
		pText--;
	}
	
	public int reserve(){
		for(int i=0;i<33;i++)
	    {
	        if(strToken.equals(key[i])){
	        	return i;
	        }
	    }
	    return -1;
	}
	
	public void writeToFile(int code, String strToken, int line){
		String fileStr=code+"\t"+strToken;//+" "+line;
		//System.out.println(fileStr);
		BufferedWriter out=null;
		try {
			out=new BufferedWriter(new OutputStreamWriter(new FileOutputStream("lexical.txt",true)));//׷��
			out.write(fileStr);
			out.newLine();
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			try {
				out.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	public int findSymbol(String str){
		for(int i=0;i<26;i++)
	    {
	        if(str.equals(symbol[i]))  return i+37;
	    }
	    return -1;
	}
	
	public void myLexer() throws IOException{
		this.read();
		while(pText<text.length()){
			this.analyse();
		}
	}
}