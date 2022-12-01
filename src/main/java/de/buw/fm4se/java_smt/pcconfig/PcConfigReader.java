package de.buw.fm4se.java_smt.pcconfig;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class PcConfigReader {
	private static final String componentsFile = "components.csv";
	private static final String constraintsFile = "constraints.csv";
	
	public static Map<String, Integer> getComponents(String category) {
		Map<String, Integer> cmps = new LinkedHashMap<String, Integer>();
		try {
			for (String line : Files.readAllLines(Paths.get(componentsFile))) {
				String[] ls = line.split(",");
				if (ls.length == 3) {					
					if (ls[0].trim().equalsIgnoreCase(category.trim())) {
						cmps.put(ls[1].trim(), Integer.parseInt(ls[2].trim()));
					}
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		return cmps;
	}
	
	public static List<String[]> getConstraints(String kind) {
		List<String[]> pairs = new ArrayList<>();
		try {
			for (String line : Files.readAllLines(Paths.get(constraintsFile))) {
				String[] ls = line.split(",");
				if (ls.length == 3) {					
					if (ls[0].trim().equalsIgnoreCase(kind)) {
						pairs.add(new String[] {ls[1].trim(), ls[2].trim()});
					}
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		return pairs;
	}
	
	
}
