package syntax;

public class One {
	public static void main(String arg[]){
		String s=".E -";
		int pointPos = s.indexOf(".");//�ҵ�.��λ��,��s'->.s ������ֵΪ0
		int spacePos = s.indexOf(" ", pointPos);//��first����λ�ã���s'->.s ������ֵΪ-1
		String nextStr = s.substring(pointPos +1,spacePos);//��s'->s.
		String searchStr = s.substring(spacePos + 1);
		System.out.println(pointPos);
		System.out.println(spacePos);
		System.out.println(nextStr);
		System.out.println(searchStr);
		
		String nowstring = null;//һ��һ������
		String nextstring = null;
		int spos = -1;
		spos = searchStr.indexOf(" ");
		if (spos == -1){//����������
			nowstring = searchStr.substring(0);
			nextstring = "";
		}else{
			nowstring = searchStr.substring(0, spos);
			nextstring = searchStr.substring(spos + 1);
		}
		System.out.println(spos);
		System.out.println(nowstring);
		System.out.println(nextstring);
	}

}
